import data.non_neg
import data.cpi.name
import order.lexicographic

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi

/-- A prefix expression. This can either be one of:

  - A communication prefix (send a series of variables on a channel, and then
    recieve, binding $n$ variables).

  - A spontanious or silent prefix: a spontanious reaction with some rate $k$.
    Used to model when a molecule may decompose into a simpler one.

  The prefix is parameterised by two contexts: the context it exists in, and the
  context resulting from binding this prefix expression. While it would be
  possible to do this with some "augment" function, it ends up complicating the
  type system a little, as you end up with weird unification constraints.
-/
inductive prefix_expr : context → (context → context) → Type
| communicate {Γ} (a :  name Γ) (b : list (name Γ)) (y : ℕ) : prefix_expr Γ (context.extend y)
| spontanious {Γ} (k : ℝ≥0) : prefix_expr Γ id

-- Define some additional notation, and sugar
notation a `#(` b ` ; ` y `)` := prefix_expr.communicate a b y
notation a `#(` y `)` := prefix_expr.communicate a [] y
notation a `#<` b `>` := prefix_expr.communicate a b 0
notation a `#` := prefix_expr.communicate a [] 0

notation `τ@`:max k:max := prefix_expr.spontanious k

namespace prefix_expr
  section rename
    /-- Apply a renaming function to a prefix. -/
    def rename : Π {Γ Δ : context} {f}, (name Γ → name Δ) → prefix_expr Γ f → prefix_expr Δ f
      | Γ Δ f ρ (a#(b; y)) := (ρ a)#(list.map ρ b; y)
      | Γ Δ f ρ τ@k := τ@k

    /-- Scope extension for prefix expressions. Given a renaming function, return
        the same function lifted for the variables bound by this prefix. -/
    def ext :
      Π {Γ Δ η : context} {f} (π : prefix_expr η f)
      , (name Γ → name Δ)
      → name (f Γ) → name (f Δ)
    | Γ Δ ._ ._ (a#(b; y)) ρ α := name.ext ρ α
    | Γ Δ ._ ._ τ@k ρ α := ρ α

    /-- Extending with the identity does nothing. -/
    lemma ext_identity :
      ∀ {Γ η : context} {f} (π : prefix_expr η f) (α : name (f Γ))
      , ext π id α = α
    | Γ η ._ (a#(b; y)) α := name.ext_identity α
    | Γ η ._ τ@k name := rfl

    /-- Extending with the identity yields the identity function. -/
    lemma ext_id : ∀ {Γ η : context} {f} (π : prefix_expr η f), @ext Γ Γ η f π id = id
    | Γ η f π := funext (ext_identity π)

    /-- Composing extensions is equivalent extending a composition. -/
    lemma ext_compose :
      ∀ {Γ Δ η φ} {f} (ρ : name Γ → name Δ) (σ : name Δ → name η)
        (π : prefix_expr φ f) (α : name (f Γ))
      , ext π σ (ext π ρ α) = ext π (σ ∘ ρ) α
    | Γ Δ η φ f ρ σ (a#(b; y)) α := name.ext_compose ρ σ α
    | Γ Δ η φ f ρ σ τ@k α := rfl

    /-- Composing extensions is equivalent extending a composition. -/
    lemma ext_comp :
      ∀ {Γ Δ η φ} {f} (ρ : name Γ → name Δ) (σ : name Δ → name η) (π : prefix_expr φ f)
      , (ext π σ ∘ ext π ρ) = ext π (σ ∘ ρ)
    | Γ Δ η φ f ρ σ π := funext (ext_compose ρ σ π)

    /-- Extending with a renamed prefix has the same effect as the original one. -/
    lemma rename_ext :
      ∀ {Γ Δ η φ} {f} (ρ : name Γ → name Δ) (σ : name η → name φ) (π : prefix_expr Γ f)
      , @ext η φ Γ f π σ = (ext (rename ρ π) σ)
    | Γ Δ η φ f ρ σ (a#(b; y)) := funext (λ α, rfl)
    | Γ Δ η φ f ρ σ τ@k := funext (λ α, rfl)

    /-- Renaming with the identity function does nothing. -/
    lemma rename_id : ∀ {Γ} {f} (π : prefix_expr Γ f), rename id π = π
    | Γ ._ (a#(b; y)) := by simp [rename]
    | Γ ._ τ@k := rfl

    /-- Renaming twice is the same as renaming with a composed function. -/
    lemma rename_compose :
      ∀ {Γ Δ η} {f} (ρ : name Γ → name Δ) (σ : name Δ → name η) (π : prefix_expr Γ f)
      , rename σ (rename ρ π) = rename (σ ∘ ρ) π
    | Γ Δ η f ρ σ (a#(b; y)) := by simp [rename]
    | Γ Δ η f ρ σ (τ@_) := rfl
  end rename

  section ordering
    /-- A wrapper for prefixed expressions, which hides the extension function.

        This is suitable for comparing prefixes. -/
    inductive wrap : context → Type
    | intro {Γ} {f} (π : prefix_expr Γ f) : wrap Γ

    protected def le {Γ} : wrap Γ → wrap Γ → Prop
    | ⟨ a#(b; y) ⟩ ⟨ a'#(b'; y') ⟩ :=
      let order := (@lex_has_le (name Γ) (lex (list (name Γ)) ℕ) _ lex_preorder) in
      @has_le.le _ order (a, b, y) (a', b', y')
    | ⟨ _#(_; _) ⟩ ⟨ τ@_ ⟩ := true
    | ⟨ τ@_ ⟩ ⟨ _#(_; _) ⟩ := false
    | ⟨ τ@k ⟩ ⟨ τ@k' ⟩ := k ≤ k'

    protected theorem le_refl {Γ} : ∀ (a : wrap Γ), prefix_expr.le a a
    | ⟨ a#(b; y) ⟩ := by simp only [prefix_expr.le]
    | ⟨ τ@k ⟩ := by unfold prefix_expr.le

    protected theorem le_trans {Γ} :
      ∀ (a b c : wrap Γ)
      , prefix_expr.le a b → prefix_expr.le b c → prefix_expr.le a c
    | ⟨ a1#(b1; y1) ⟩ ⟨ a2#(b2; y2) ⟩ ⟨ a3#(b3; y3) ⟩ h12 h23 := begin
        simp only [prefix_expr.le] at h12 h23 ⊢,
        from preorder.le_trans _ _ _ h12 h23
      end
    | ⟨ τ@k1 ⟩ ⟨ τ@k2 ⟩ ⟨ τ@k3 ⟩ h12 h23 := begin
        unfold prefix_expr.le at h12 h23 ⊢,
        from preorder.le_trans _ _ _ h12 h23,
      end
    | ⟨ a#(b; y) ⟩ ⟨ _#(_ ; _) ⟩ ⟨ τ@k ⟩ h12 h23 := by unfold prefix_expr.le
    | ⟨ a#(b; y) ⟩ ⟨ τ@_ ⟩ ⟨ τ@k ⟩ h12 h23 := by unfold prefix_expr.le
    | ⟨ τ@k ⟩ ⟨ a#(b;y) ⟩ _ h12 h23 := by { unfold prefix_expr.le at h12, contradiction }

    protected theorem le_total {Γ} : ∀ (a b : wrap Γ), prefix_expr.le a b ∨ (prefix_expr.le b a)
    | ⟨ a#(b; y) ⟩ ⟨ a'#(b'; y') ⟩ := by { simp only [prefix_expr.le], from linear_order.le_total _ _ }
    | ⟨ a#(b; y) ⟩ ⟨ τ@k ⟩ := by { unfold prefix_expr.le, simp only [true_or] }
    | ⟨ τ@k ⟩ ⟨ a#(b; y) ⟩ := by { unfold prefix_expr.le, simp only [or_true] }
    | ⟨ τ@k ⟩ ⟨ τ@k' ⟩ := by { unfold prefix_expr.le, from linear_order.le_total k k' }

    protected theorem le_antisymm {Γ} : ∀ (a b : wrap Γ), prefix_expr.le a b → prefix_expr.le b a → a = b
    | ⟨ a#(b; y) ⟩ ⟨ a'#(b'; y') ⟩ ab ba := begin
        simp only [prefix_expr.le] at ab ba,
        have eq : (⟨ a, b, y ⟩ : lex _ (lex _ _)) = ⟨ a', b', y' ⟩,
        from @linear_order.le_antisymm (lex _ _)
          (@lex_linear_order (name Γ) (lex (list (name Γ)) ℕ) _ _)
          (a, b, y) (a', b', y') ab ba,
        simp at eq, simp [eq],
        have h : y = y' := by simp only [eq],
        subst h
      end
    | ⟨ τ@k ⟩ ⟨ a#(b; y) ⟩ ab _ := by { unfold prefix_expr.le at ab, contradiction }
    | ⟨ a#(b; y) ⟩ ⟨ τ@k ⟩ _ ba := by { unfold prefix_expr.le at ba, contradiction }
    | ⟨ τ@k ⟩ ⟨ τ@k' ⟩ ab ba := begin
        unfold prefix_expr.le at ab ba,
        have eq : k = k', from linear_order.le_antisymm _ _ ab ba, subst eq
      end

    protected noncomputable def decidable_le {Γ} : ∀ (a b : wrap Γ), decidable (prefix_expr.le a b)
    | ⟨ a#(b; y) ⟩ ⟨ a'#(b'; y') ⟩ := by { unfold prefix_expr.le, apply_instance }
    | ⟨ _#(_; _) ⟩ ⟨ τ@_ ⟩ := is_true true.intro
    | ⟨ τ@_ ⟩ ⟨ _#(_; _) ⟩ := is_false not_false
    | ⟨ τ@k ⟩ ⟨ τ@k' ⟩ := by { unfold prefix_expr.le, apply_instance }

    /-- Somewhat bizzare helper function to show the impossible cannot happen.

        It's hopefully possible to remove this I just haven't worked out how. -/
    private def no_extend : ∀ {y Γ}, ¬ (context.extend y Γ = Γ)
    | y (context.nil) eq := by contradiction
    | y (context.extend n Γ) eq := begin
        simp only [] at eq,
        have : y = n := and.left eq, subst this,
        have : context.extend y Γ = Γ := and.right eq,
        from no_extend this
      end

    protected noncomputable def decidable_eq {Γ} : ∀ (a b : wrap Γ), decidable (a = b)
    | ⟨ a#(b; y) ⟩ ⟨ a'#(b'; y') ⟩ :=
        if hy : y = y'
        then if ha : a = a'
             then if hb : b = b'
                  then is_true (by rw [hy, ha, hb])
                  else is_false (begin rw [hy], simp [hb] end)
            else is_false (begin rw [hy], simp [ha] end)
        else is_false (λ x, begin
          simp only [] at x,
          -- We only have (context.extend y = context.extend y') - thus we need
          -- to saturate the call with congr_fun, and then derive y = y'.
          have : y = y' := and.left (context.extend.inj (congr_fun (and.left x) Γ)),
          contradiction
        end)
    | ⟨ a#(b; y) ⟩ ⟨ τ@k ⟩ := is_false (λ x, begin
        simp only [] at x,
        have h := congr_fun (and.left x) Γ, simp at h,
        from no_extend h
      end)
    | ⟨ τ@k ⟩ ⟨ a#(b; y) ⟩ := is_false (λ x, begin
        simp only [] at x,
        have h := congr_fun (and.left x) Γ,
        from no_extend (symm h)
      end)
    | ⟨ τ@k ⟩ ⟨ τ@k' ⟩ :=
      if h : k = k'
      then is_true (by rw [h])
      else is_false (λ x, begin simp at x, contradiction end)

    noncomputable instance {Γ} : decidable_linear_order (wrap Γ) :=
      { le := prefix_expr.le,
        le_refl := prefix_expr.le_refl,
        le_trans := prefix_expr.le_trans,
        le_total := prefix_expr.le_total,
        le_antisymm := prefix_expr.le_antisymm,
        decidable_eq := prefix_expr.decidable_eq,
        decidable_le := prefix_expr.decidable_le,
      }
  end ordering
end prefix_expr

end cpi

#sanity_check
