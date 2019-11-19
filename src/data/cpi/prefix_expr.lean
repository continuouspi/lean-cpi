import data.cpi.name
import data.list.witness order.lexicographic

namespace cpi

-- 𝔸𝔹ℂ𝔻𝔼𝔽𝔾ℍ𝕀𝕁𝕂𝕃𝕄ℕ𝕆ℙℚℝ𝕊𝕋𝕌𝕍𝕎𝕏𝕐ℤ
/-- A prefix expression. This can either be one of:

  - A communication prefix (send a series of variables on a channel, and then
    recieve, binding $n$ variables).

  - A spontanious or silent prefix: a spontanious reaction with some rate $k$.
    Used to model when a molecule may decompose into a simpler one.

  The prefix is parameterised by two types: the context it exists in, a function
  which augments an arbitrary context with variables bound by this prefix.

  While it is possible to do without the second parameter, this introduces many
  complexities to the proof when renaming, as you need to
  `augment (rename π) = augment π', while preserving type safety.
-/
inductive prefix_expr (ℍ : Type) : context → (context → context) → Type
| communicate {} {Γ} (a :  name Γ) (b : list (name Γ)) (y : ℕ) : prefix_expr Γ (context.extend y)
| spontanious {} {Γ} (k : ℍ) : prefix_expr Γ id

variables {ℍ : Type}

-- Define some additional notation, and sugar
notation a `#(` b ` ; ` y `)` := prefix_expr.communicate a b y
notation a `#(` y `)` := prefix_expr.communicate a [] y
notation a `#<` b `>` := prefix_expr.communicate a b 0
notation a `#` := prefix_expr.communicate a [] 0

notation `τ@`:max k:max := prefix_expr.spontanious k

namespace prefix_expr
  /- Just show that prefixes form a decidable linear order. -/
  section ordering
    /-- A wrapper for prefixed expressions, which hides the extension function.

        This is suitable for comparing prefixes. -/
    inductive wrap (ℍ : Type) : context → Type
    | intro {} {Γ} {f} (π : prefix_expr ℍ Γ f) : wrap Γ

    protected def le {Γ} [has_le ℍ] : wrap ℍ Γ → wrap ℍ Γ → Prop
    | ⟨ a#(b; y) ⟩ ⟨ a'#(b'; y') ⟩ :=
      let order := (@lex_has_le (name Γ) (lex (list (name Γ)) ℕ) _ lex_preorder) in
      @has_le.le _ order (a, b, y) (a', b', y')
    | ⟨ _#(_; _) ⟩ ⟨ τ@_ ⟩ := true
    | ⟨ τ@_ ⟩ ⟨ _#(_; _) ⟩ := false
    | ⟨ τ@k ⟩ ⟨ τ@k' ⟩ := k ≤ k'

    protected theorem le_refl {Γ} [preorder ℍ] : ∀ (a : wrap ℍ Γ), prefix_expr.le a a
    | ⟨ a#(b; y) ⟩ := by simp only [prefix_expr.le]
    | ⟨ τ@k ⟩ := by unfold prefix_expr.le

    protected theorem le_trans {Γ} [preorder ℍ]:
      ∀ (a b c : wrap ℍ Γ)
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

    protected theorem le_total {Γ} [linear_order ℍ] :
      ∀ (a b : wrap ℍ Γ), prefix_expr.le a b ∨ (prefix_expr.le b a)
    | ⟨ a#(b; y) ⟩ ⟨ a'#(b'; y') ⟩ := by { simp only [prefix_expr.le], from linear_order.le_total _ _ }
    | ⟨ a#(b; y) ⟩ ⟨ τ@k ⟩ := by { unfold prefix_expr.le, simp only [true_or] }
    | ⟨ τ@k ⟩ ⟨ a#(b; y) ⟩ := by { unfold prefix_expr.le, simp only [or_true] }
    | ⟨ τ@k ⟩ ⟨ τ@k' ⟩ := by { unfold prefix_expr.le, from linear_order.le_total k k' }

    protected theorem le_antisymm {Γ} [linear_order ℍ]:
      ∀ (a b : wrap ℍ Γ), prefix_expr.le a b → prefix_expr.le b a → a = b
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

    protected def decidable_le {Γ} [has_le ℍ] [@decidable_rel ℍ (≤)] :
      ∀ (a b : wrap ℍ Γ), decidable (prefix_expr.le a b)
    | ⟨ a#(b; y) ⟩ ⟨ a'#(b'; y') ⟩ := by { unfold prefix_expr.le, apply_instance }
    | ⟨ _#(_; _) ⟩ ⟨ τ@_ ⟩ := is_true true.intro
    | ⟨ τ@_ ⟩ ⟨ _#(_; _) ⟩ := is_false not_false
    | ⟨ τ@k ⟩ ⟨ τ@k' ⟩ := by { unfold prefix_expr.le, apply_instance }

    /-- Somewhat bizzare helper function to show the impossible cannot happen.

        It's hopefully possible to remove this I just haven't worked out how. -/
    private lemma no_extend {y : ℕ} : ∀ {Γ}, ¬ (context.extend y Γ = Γ)
    | context.nil eq := by contradiction
    | (context.extend n Γ) eq := begin
        simp only [] at eq,
        have : y = n := and.left eq, subst this,
        have : context.extend y Γ = Γ := and.right eq,
        from no_extend this
      end

    protected def decidable_eq {Γ} [decidable_eq ℍ] : decidable_eq (wrap ℍ Γ)
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

    instance {Γ} [decidable_linear_order ℍ] : decidable_linear_order (wrap ℍ Γ) :=
      { le := prefix_expr.le,
        le_refl := prefix_expr.le_refl,
        le_trans := prefix_expr.le_trans,
        le_total := prefix_expr.le_total,
        le_antisymm := prefix_expr.le_antisymm,
        decidable_eq := prefix_expr.decidable_eq,
        decidable_le := prefix_expr.decidable_le,
      }
  end ordering

  section free
    /-- Determine if any variable with a given level occurs within this prefix.
    -/
    def free_in : ∀ {Γ} {f}, level Γ → prefix_expr ℍ Γ f → Prop
    | ._ ._ l (a#(b; y)) := l ∈ a ∨ ∃ x ∈ b, l ∈ x
    | ._ ._ l τ@_ := false

    instance {Γ} {f} : has_mem (level Γ) (prefix_expr ℍ Γ f) := ⟨ free_in ⟩

    private def free_in_decide : ∀ {Γ} {f}
      (l : level Γ) (π : prefix_expr ℍ Γ f), decidable (free_in l π)
    | Γ ._ l (a#(b; y)) := if h : l ∈ a ∨ ∃ x ∈ b, l ∈ x then is_true h else is_false h
    | ._ ._ l τ@_ := decidable.false

    instance free_in.decidable {Γ} {f} {l} {π : prefix_expr ℍ Γ f}
      : decidable (free_in l π)
      := free_in_decide l π
  end free

  /- Renaming and extension.

      The extension sections are largely similar to that in data.cpi.name - see
      there for an explanation of some of the decisions made. -/
  section rename
    /-- Raise a level according to this prefix's context extension function. -/
    def raise :
      ∀ {Γ η} {f} (π : prefix_expr ℍ η f)
      , level Γ → level (f Γ)
    | Γ ._ ._ (a#(b; y)) l := level.extend l
    | Γ ._ ._ τ@_ l := l

    /-- Rename all names within a prefix expression, providing some witness that
        this variable is free within it. -/
    def rename_with {Γ Δ} :
      Π {f} (π : prefix_expr ℍ Γ f)
      , (Π (a : name Γ), name.to_level a ∈ π → name Δ) → prefix_expr ℍ Δ f
    | f (a#(b; y)) ρ :=
      let a' := ρ a (or.inl (name.to_level_at a)) in
      let b' := list.map_witness b
        (λ x mem, ρ x (or.inr ⟨ x, mem, name.to_level_at x ⟩))
      in
      a'#( b' ; y)
    | f τ@k ρ := τ@k

    /-- Simple renaming function, not taking any witness. -/
    @[reducible]
    def rename {Γ Δ} {f} (ρ : name Γ → name Δ) (π : prefix_expr ℍ Γ f)
      : prefix_expr ℍ Δ f
      := rename_with π (λ a _, ρ a)

    /-- Renaming with the identity function does nothing. -/
    lemma rename_with_id {Γ} : ∀ {f} (π : prefix_expr ℍ Γ f)
      , rename_with π (λ a _, a) = π
    | ._ (a#(b; y)) := by simp [rename_with]
    | ._ τ@k := rfl

    /-- Renaming with the identity function is the identity. -/
    lemma rename_id {Γ} {f} (π : prefix_expr ℍ Γ f) : rename id π = π
      := rename_with_id π

    /-- Renaming twice is the same as renaming with a composed function. -/
    lemma rename_with_compose {Γ Δ η} :
      ∀ {f} (π : prefix_expr ℍ Γ f)
        (ρ : Π (a : name Γ), name.to_level a ∈ π → name Δ)
        (σ : name Δ → name η)
      , rename σ (rename_with π ρ) = rename_with π (λ a free, σ (ρ a free))
    | f (a#(b; y)) ρ σ := by simp [rename_with, rename, list.map_witness_to_map]
    | f (τ@_) ρ σ := rfl

    /-- Renaming twice is the same as renaming with a composed function. -/
    lemma rename_compose {Γ Δ η} {f}
        (π : prefix_expr ℍ Γ f) (ρ : name Γ → name Δ) (σ : name Δ → name η)
      : rename σ (rename ρ π) = rename (σ ∘ ρ) π
    := rename_with_compose π _ _

    /-- Wrap a renaming function, making it suitable for a nested context. -/
    def ext_with {Γ Δ η} :
      ∀ {f} (π : prefix_expr ℍ η f)
        (P : level (f Γ) → Prop)
        (ρ : Π (x : name Γ), P (prefix_expr.raise π (name.to_level x)) → name Δ)
      , Π (x : name (f Γ)), P (name.to_level x) → name (f Δ)
    | f (_#(_; y)) P ρ a p := name.ext_with P ρ a p
    | f τ@_ P ρ a p := ρ a p

    /-- Extending with the identity does nothing. -/
    lemma ext_with_identity :
      ∀ {Γ η} {f} (π : prefix_expr ℍ η f)
        (P : level (f Γ) → Prop)
        (a : name (f Γ)) (p : P (name.to_level a))
      , ext_with π P (λ x _, x) a p = a
    | Γ η ._ (_#(_; _)) P a p := name.ext_with_identity P a p
    | Γ η ._ τ@k P a p := rfl

    /-- Extending with the identity does nothing. -/
    lemma ext_with_id {Γ η} {f}
        (π : prefix_expr ℍ η f) (P : level (f Γ) → Prop)
      : ext_with π P (λ x _, x) = λ x _, x
      := funext $ λ a, funext (ext_with_identity π P a)

    /-- Wrap a simple renaming function, making it suitable for a nested context. -/
    def ext {Γ Δ η} {f} (π : prefix_expr ℍ η f) (ρ : name Γ → name Δ)
          : name (f Γ) → name (f Δ)
    | a := ext_with π (λ _, true) (λ x _, ρ x) a true.intro

    /-- Extending with the identity does nothing. -/
    lemma ext_identity {Γ η} {f} (π : prefix_expr ℍ η f) (a : name (f Γ))
      : ext π id a = a := ext_with_identity π _ a _

    /-- Extending with the identity yields the identity function. -/
    lemma ext_id : ∀ {Γ η} {f} (π : prefix_expr ℍ η f), @ext ℍ Γ Γ η f π id = id
    | Γ η f π := funext (ext_identity π)

    /-- Composing extensions is equivalent extending a composition. -/
    lemma ext_with_compose :
      ∀ {Γ Δ η φ} {f} (π : prefix_expr ℍ φ f)
        (P : level (f Γ) → Prop)
        (ρ : Π (x : name Γ), P (raise π (name.to_level x)) → name Δ)
        (σ : name Δ → name η)
        (a : name (f Γ)) (p : P (name.to_level a))
      , ext π σ (ext_with π P ρ a p) = ext_with π P (λ a p, σ (ρ a p)) a p
    | Γ Δ η φ f (_#(_;_)) P ρ σ a p := name.ext_with_compose P ρ σ a p
    | Γ Δ η φ f τ@_ P ρ σ _ _ := rfl

    /-- Composing extensions is equivalent extending a composition. -/
    lemma ext_with_comp {Γ Δ η φ} {f} (π : prefix_expr ℍ φ f)
        (P : level (f Γ) → Prop)
        (ρ : Π (x : name Γ), P (raise π (name.to_level x)) → name Δ)
        (σ : name Δ → name η)
      : (λ a p, ext π σ (ext_with π P ρ a p)) = ext_with π P (λ a p, σ (ρ a p))
      := funext $ λ a, funext (ext_with_compose π P ρ σ a)

    /-- Composing extensions is equivalent extending a composition. -/
    lemma ext_compose :
      ∀ {Γ Δ η φ} {f} (ρ : name Γ → name Δ) (σ : name Δ → name η)
        (π : prefix_expr ℍ φ f) (α : name (f Γ))
      , ext π σ (ext π ρ α) = ext π (σ ∘ ρ) α
    | Γ Δ η φ f ρ σ (a#(b; y)) α := name.ext_compose ρ σ α
    | Γ Δ η φ f ρ σ τ@k α := rfl

    /-- Composing extensions is equivalent extending a composition. -/
    lemma ext_comp :
      ∀ {Γ Δ η φ} {f} (ρ : name Γ → name Δ) (σ : name Δ → name η)
        (π : prefix_expr ℍ φ f)
      , (ext π σ ∘ ext π ρ) = ext π (σ ∘ ρ)
    | Γ Δ η φ f ρ σ π := funext (ext_compose ρ σ π)

    /-- Rewrite one ext_with to another -/
    lemma ext_with_discard :
      ∀ {Γ Δ η} {f} (π : prefix_expr ℍ η f)
        (P : level (f Γ) → Prop)
        (ρ : name Γ → name Δ)
      , (ext_with π P (λ a _, ρ a))
      = (λ a _, ext_with π (λ _x, true) (λ x _, ρ x) a true.intro)
    | Γ Δ η f (a'#(b; y)) P ρ := funext $ λ a, funext $ λ free, begin
        have : (λ (a : name Γ) (_x : P (@raise ℍ _ _ _ (a'#(b ; y)) (name.to_level a))), ρ a)
             = (λ (a : name Γ) (_x : P (level.extend (name.to_level a))), ρ a)
             := rfl,
        unfold ext_with,
        rw [this, name.ext_with_discard P],
      end
    | Γ Δ η f τ@_ P ρ := funext $ λ a, funext $ λ free, rfl

    /-- Raising with a renamed prefix has the same effect as the original one. -/
    lemma rename_with_raise
        {Γ Δ η} {f} (π : prefix_expr ℍ Γ f)
        (ρ : Π (x : name Γ), name.to_level x ∈ π → name Δ)
        (l : level η)
      : raise π l = raise (rename_with π ρ) l
      := by { cases π; from rfl }

    /-- Extending with a renamed prefix has the same effect as the original one. -/
    lemma rename_with_ext_with
        {Γ Δ η φ} {f} (π : prefix_expr ℍ η f)
        (P : level (f Γ) → Prop)
        (ρ : name Γ → name Δ)
        (σ : Π (x : name η), name.to_level x ∈ π → name φ)
      : ext_with (rename_with π σ) P (λ a _, ρ a) = ext_with π P (λ a _, ρ a)
      := funext $ λ a, funext $ λ free, by { cases π; from rfl }

    /-- Extending with a renamed prefix has the same effect as the original one. -/
    lemma rename_ext
        {Γ Δ η φ} {f} (ρ : name Γ → name Δ) (σ : name η → name φ)
        (π : prefix_expr ℍ Γ f)
      : @ext ℍ η φ Γ f π σ = (ext (rename ρ π) σ)
      := funext $ λ a, by { cases π; from rfl }
  end rename

  section rename_equations
    variables {Γ Δ : context} {ρ : name Γ → name Δ}

    @[simp]
    lemma rename_communicate (a :  name Γ) (b : list (name Γ)) (y : ℕ)
      : rename ρ (a#(b; y) : prefix_expr ℍ _ _) = ((ρ a)#(list.map ρ b; y))
      := by simp [rename, rename_with, list.map_witness_to_map]

    @[simp]
    lemma rename_spontanious (k : ℍ)
      : rename ρ τ@k = τ@k
      := by simp only [rename, rename_with]

    @[simp]
    lemma ext_communicate {η} (a :  name η) (b : list (name η)) (y : ℕ)
      : ext (a#(b; y) : prefix_expr ℍ _ _) ρ = name.ext ρ
      := funext $ λ x, by unfold ext ext_with

    @[simp]
    lemma ext_spontanious {η} (k : ℍ)
      : ext (@spontanious ℍ η k) ρ = ρ
      := funext $ λ x, by unfold ext ext_with

    private lemma rename_inj {Γ Δ} {ρ : name Γ → name Δ} (inj : function.injective ρ)
      : ∀ {f₁ f₂} {π₁ : prefix_expr ℍ Γ f₁} {π₂ : prefix_expr ℍ Γ f₂}
      , wrap.intro (rename ρ π₁) = wrap.intro (rename ρ π₂)
      → π₁ == π₂
    | _ _ (a#(b; y)) (a'#(b'; y')) eq := begin
        simp only [rename_communicate] at eq,
        rcases eq with ⟨ eqC, eqπ ⟩,

        have : y = y' := (context.extend.inj (congr_fun eqC Γ)).left, cases this,
        simp only [heq_iff_eq] at eqπ ⊢,

        from ⟨ inj eqπ.left, list.injective_map_iff.mpr inj eqπ.right ⟩,
      end
    | _ _ (a#(b; y)) τ@k eq := begin
      simp only [rename_communicate, rename_spontanious] at eq,
        rcases eq with ⟨ eqC, eqπ ⟩,
        from absurd (congr_fun eqC Γ) no_extend,
    end
    | _ _ τ@k (a#(b; y)) eq := begin
        simp only [rename_communicate, rename_spontanious] at eq,
        rcases eq with ⟨ eqC, eqπ ⟩,
        from absurd (congr_fun (symm eqC) Γ) no_extend,
      end
    | _ _ τ@k τ@k' eq := begin
        simp only [rename_spontanious] at eq,
        rcases eq with ⟨ eqC, eqπ ⟩,
        cases eqπ, from heq.refl _,
      end

    lemma rename.inj {Γ Δ} {ρ : name Γ → name Δ} (inj : function.injective ρ)
      : ∀ {f}, function.injective (@rename ℍ Γ Δ f ρ)
    | f π₁ π₂ eq := eq_of_heq (rename_inj inj (congr_arg wrap.intro eq))

    lemma ext.inj {Γ Δ η} {ρ : name Γ → name Δ}
      : ∀ {f} (π : prefix_expr ℍ η f), function.injective ρ → function.injective (ext π ρ)
    | ._ (_#(_; y)) inj a b eq := begin
        simp only [ext_communicate] at eq,
        from name.ext.inj inj eq,
      end
    | ._ (τ@_) inj a b eq := by { simp only [ext_spontanious] at eq, from inj eq, }
  end rename_equations

end prefix_expr

end cpi

#lint
