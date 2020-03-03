import data.cpi.name
import data.list.witness

namespace cpi

/-- A telescope may extend a context by 0 or 1 levels. This is effectively a
    function on contexts, but having it be inductive allows us to case split on
    it, simplifying some proofs. -/
@[derive decidable_eq]
inductive telescope : Type
| extend : ℕ → telescope
| preserve : telescope

/-- Apply a telescope to a context. -/
def telescope.apply : telescope → context → context
| (telescope.extend n) Γ := context.extend n Γ
| telescope.preserve Γ := Γ

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
@[derive decidable_eq]
inductive prefix_expr (ℍ : Type) : context → telescope → Type
| communicate {} {Γ} (a :  name Γ) (b : list (name Γ)) (y : ℕ) : prefix_expr Γ (telescope.extend y)
| spontanious {} {Γ} (k : ℍ) : prefix_expr Γ telescope.preserve

variables {ℍ : Type}

-- Define some additional notation, and sugar
notation a `#(` b ` ; ` y `)` := prefix_expr.communicate a b y
notation a `#(` y `)` := prefix_expr.communicate a [] y
notation a `#⟨` b `⟩` := prefix_expr.communicate a b 0
notation a `#` := prefix_expr.communicate a [] 0

notation `τ@`:max k:max := prefix_expr.spontanious k

namespace prefix_expr
    /-- A wrapper for prefixed expressions, which hides the extension function.

        This is suitable for comparing prefixes. -/
    inductive wrap (ℍ : Type) : context → Type
    | intro {} {Γ} {f} (π : prefix_expr ℍ Γ f) : wrap Γ

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
      , level Γ → level (f.apply Γ)
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
        (P : level (f.apply Γ) → Prop)
        (ρ : Π (x : name Γ), P (prefix_expr.raise π (name.to_level x)) → name Δ)
      , Π (x : name (f.apply Γ)), P (name.to_level x) → name (f.apply Δ)
    | f (_#(_; y)) P ρ a p := name.ext_with P ρ a p
    | f τ@_ P ρ a p := ρ a p

    /-- Extending with the identity does nothing. -/
    lemma ext_with_identity :
      ∀ {Γ η} {f} (π : prefix_expr ℍ η f)
        (P : level (f.apply Γ) → Prop)
        (a : name (f.apply Γ)) (p : P (name.to_level a))
      , ext_with π P (λ x _, x) a p = a
    | Γ η ._ (_#(_; _)) P a p := name.ext_with_identity P a p
    | Γ η ._ τ@k P a p := rfl

    /-- Extending with the identity does nothing. -/
    lemma ext_with_id {Γ η} {f}
        (π : prefix_expr ℍ η f) (P : level (f.apply Γ) → Prop)
      : ext_with π P (λ x _, x) = λ x _, x
      := funext $ λ a, funext (ext_with_identity π P a)

    /-- Wrap a simple renaming function, making it suitable for a nested context. -/
    def ext {Γ Δ η} {f} (π : prefix_expr ℍ η f) (ρ : name Γ → name Δ)
          : name (f.apply Γ) → name (f.apply Δ)
    | a := ext_with π (λ _, true) (λ x _, ρ x) a true.intro

    /-- Extending with the identity does nothing. -/
    lemma ext_identity {Γ η} {f} (π : prefix_expr ℍ η f) (a : name (f.apply Γ))
      : ext π id a = a := ext_with_identity π _ a _

    /-- Extending with the identity yields the identity function. -/
    lemma ext_id : ∀ {Γ η} {f} (π : prefix_expr ℍ η f), @ext ℍ Γ Γ η f π id = id
    | Γ η f π := funext (ext_identity π)

    /-- Composing extensions is equivalent extending a composition. -/
    lemma ext_with_compose :
      ∀ {Γ Δ η φ} {f} (π : prefix_expr ℍ φ f)
        (P : level (f.apply Γ) → Prop)
        (ρ : Π (x : name Γ), P (raise π (name.to_level x)) → name Δ)
        (σ : name Δ → name η)
        (a : name (f.apply Γ)) (p : P (name.to_level a))
      , ext π σ (ext_with π P ρ a p) = ext_with π P (λ a p, σ (ρ a p)) a p
    | Γ Δ η φ f (_#(_;_)) P ρ σ a p := name.ext_with_compose P ρ σ a p
    | Γ Δ η φ f τ@_ P ρ σ _ _ := rfl

    /-- Composing extensions is equivalent extending a composition. -/
    lemma ext_with_comp {Γ Δ η φ} {f} (π : prefix_expr ℍ φ f)
        (P : level (f.apply Γ) → Prop)
        (ρ : Π (x : name Γ), P (raise π (name.to_level x)) → name Δ)
        (σ : name Δ → name η)
      : (λ a p, ext π σ (ext_with π P ρ a p)) = ext_with π P (λ a p, σ (ρ a p))
      := funext $ λ a, funext (ext_with_compose π P ρ σ a)

    /-- Composing extensions is equivalent extending a composition. -/
    lemma ext_compose :
      ∀ {Γ Δ η φ} {f} (ρ : name Γ → name Δ) (σ : name Δ → name η)
        (π : prefix_expr ℍ φ f) (α : name (f.apply Γ))
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
        (P : level (f.apply Γ) → Prop)
        (ρ : name Γ → name Δ)
      , (ext_with π P (λ a _, ρ a))
      = (λ a _, ext_with π (λ _x, true) (λ x _, ρ x) a true.intro)
    | Γ Δ η f (a'#(b; y)) P ρ := funext $ λ a, funext $ λ free, begin
        have : (λ (a : name Γ) (_x : P (@raise ℍ _ _ _ (a'#(b ; y)) (name.to_level a))), ρ a)
             = (λ (a : name Γ) (_x : P (level.extend (name.to_level a))), ρ a)
             := rfl,
        unfold ext_with,
        rw [this, name.ext_with_discard P],
        from rfl,
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
        (P : level (f.apply Γ) → Prop)
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
      := funext $ λ x, by { unfold ext ext_with, from rfl }

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
        rcases eq with ⟨ ⟨ _ ⟩, eqπ ⟩,
        simp only [heq_iff_eq] at eqπ ⊢,
        from ⟨ inj eqπ.left, list.injective_map_iff.mpr inj eqπ.right ⟩,
      end
    | _ _ (a#(b; y)) τ@k eq := begin
      simp only [rename_communicate, rename_spontanious] at eq,
      exfalso, from eq.1,
    end
    | _ _ τ@k (a#(b; y)) eq := begin
        simp only [rename_communicate, rename_spontanious] at eq,
        exfalso, from eq.1,
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

#lint-
