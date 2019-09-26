import tactic.sanity_check data.fin

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi

/-- A context under which terms may be evaluated.

    Each level of the context holds the arity of the vector defined at that
    point. -/
@[derive decidable_eq]
inductive context
| nil : context
| extend : ℕ → context → context

/-- The set of names within the continuous-π calculus. -/
@[derive decidable_eq]
inductive name : context → Type
| zero   {Γ} {n : ℕ} : fin n → name (context.extend n Γ)
| extend {Γ} {n : ℕ} : name Γ → name (context.extend n Γ)

/-- A level a variable can occur at. -/
@[derive decidable_eq]
inductive level : context → Type
| zero   {Γ} {n} : level (context.extend n Γ)
| extend {Γ} {n} : level Γ → level (context.extend n Γ)

namespace name
  def to_level : ∀ {Γ}, name Γ → level Γ
  | ._ (zero _) := level.zero
  | ._ (extend a) := level.extend (to_level a)

  section ordering
    inductive le : ∀ {Γ}, name Γ → name Γ → Prop
    | zero {Γ} {n} {i j : fin n} :    i ≤ j → le (@zero Γ n i) (zero j)
    | one  {Γ} {n} {i : fin n} (a : name Γ) : le (@zero Γ n i) (extend a)
    | succ {Γ} {n} {a b : name Γ} :  le a b → le (@extend Γ n a) (extend b)

    protected theorem le_refl : ∀ {Γ} (α : name Γ), name.le α α
    | ._ (zero x) := le.zero (nat.le_refl x.val)
    | ._ (extend x) := le.succ (le_refl x)

    protected theorem le_trans : ∀ {Γ} (a b c : name Γ), name.le a b → name.le b c → name.le a c
    | ._ ._ ._ ._ (le.zero ab) (le.zero bc) := le.zero (preorder.le_trans _ _ _ ab bc)
    | ._ ._ ._ ._ (le.zero ab) (le.one c) := le.one c
    | ._ ._ ._ ._ (le.succ ab) (le.succ bc) := le.succ (le_trans _ _ _ ab bc)
    | ._ ._ ._ ._ (le.one β') (le.succ _) := le.one _

    protected theorem le_antisymm : ∀ {Γ} (a b : name Γ), le a b → le b a → a = b
    | ._ (zero a) (zero b) (le.zero ab) (le.zero ba) := by rw partial_order.le_antisymm _ _ ab ba
    | ._ (extend a) (extend b) (le.succ ab) (le.succ ba) := by rw le_antisymm a b ab ba

    protected theorem le_total : ∀ {Γ} (a b : name Γ), le a b ∨ le b a
    | ._ (name.zero i) (name.zero j) :=
      if h : i ≤ j
      then or.inl (le.zero h)
      else or.inr (le.zero (le_of_not_le h))
    | ._ (name.extend a) (name.extend b) :=
      match le_total a b with
      | or.inl x := or.inl (le.succ x)
      | or.inr x := or.inr (le.succ x)
      end
    | ._ (name.zero _) (name.extend _) := or.inl (le.one _)
    | ._ (name.extend _) (name.zero _) := or.inr (le.one _)

    protected def decidable_le : ∀ {Γ} (a b : name Γ), decidable (le a b)
    | ._ (name.zero i) (name.zero j) :=
      if h : i ≤ j
      then is_true (le.zero h)
      else is_false (λ x, begin cases x, contradiction end)
    | ._ (name.zero i) (name.extend a) := is_true (le.one _)
    | ._ (name.extend a) (name.zero i) := is_false (λ x, begin cases x end)
    | ._ (name.extend a) (name.extend b) :=
      match decidable_le a b with
      | is_true h := is_true (le.succ h)
      | is_false h := is_false (λ x, begin cases x, contradiction end)
      end

    instance {Γ} : decidable_linear_order (name Γ) :=
      { le := name.le,
        le_refl := name.le_refl,
        le_trans := name.le_trans,
        le_antisymm := name.le_antisymm,
        le_total := name.le_total,
        decidable_le := name.decidable_le,
        decidable_eq := by apply_instance }
  end ordering

  section free
    /-- Determine if this variable has a given level. This can be thought of
        as a preliminary to determining if a given level is free within this
        variable. -/
    def at_level : ∀ {Γ}, level Γ → name Γ → Prop
    | ._ level.zero (zero _) := true
    | ._ (level.extend l) (extend a) := at_level l a

    | ._ level.zero (extend _) := false
    | ._ (level.extend _) (zero _) := false

    instance {Γ} : has_mem (level Γ) (name Γ) := ⟨ at_level ⟩

    private def at_level_decide : ∀ {Γ} (l : level Γ) (a : name Γ), decidable (at_level l a)
    | ._ level.zero (zero _) := decidable.true
    | ._ (level.extend l) (extend a) := begin
        unfold at_level,
        from at_level_decide l a
      end
    | ._ level.zero (extend _) := decidable.false
    | ._ (level.extend _) (zero _) := decidable.false

    instance at_level.decidable {Γ} {l} {a : name Γ} : decidable (at_level l a)
      := at_level_decide l a

    /-- Any variable is always at the level provided by to_level. -/
    theorem to_level_at : ∀ {Γ} (a : name Γ), name.to_level a ∈ a
    | ._ (zero _) := by unfold to_level
    | ._ (extend n) := begin
        suffices : at_level (to_level n) n,
          unfold to_level at_level has_mem.mem,
          assumption,

        from to_level_at n
      end
  end free

  section rename
    /-- Scope extension for names. Given a renaming function, return the same
        function lifted one level.-/
    def ext_with {Γ Δ} {n}
        (P : level (context.extend n Γ) → Prop)
        (ρ : Π (x : name Γ), P (level.extend (name.to_level x)) → name Δ)
      : Π (x : name (context.extend n Γ)), P (name.to_level x) → name (context.extend n Δ)
    | (zero idx) p := zero idx
    | (extend a) p := extend (ρ a p)

    /-- Extending with the identity does nothing. -/
    lemma ext_with_identity :
      ∀ {Γ : context} {n : ℕ}
        (P : level (context.extend n Γ) → Prop)
        (a : name (context.extend n Γ)) (p : P (name.to_level a))
      , ext_with P (λ x _, x) a p = a
    | Γ n P (zero lt) _ := rfl
    | Γ n P (extend a) _ := rfl

    /-- Extending with the identity does nothing. -/
    lemma ext_with_id {Γ : context} {n : ℕ}
        (P : level (context.extend n Γ) → Prop)
      : ext_with P (λ x _, x) = λ x _, x
      := funext $ λ a, funext (ext_with_identity P a)

    /-- Scope extension for names. Given a renaming function, return the same
        function lifted one level.-/
    @[reducible]
    def ext {Γ Δ : context} {n} (ρ : name Γ → name Δ)
          : name (context.extend n Γ) → name (context.extend n Δ)
    | a := ext_with (λ _, true) (λ x p, ρ x) a true.intro

    /-- Extending with the identity does nothing. -/
    lemma ext_identity {Γ : context} {n : ℕ} (a : name (context.extend n Γ))
      : ext id a = a
      := ext_with_identity _ a _

    /-- Extending with the identity yields the identity function. -/
    lemma ext_id : ∀ {Γ : context} {n : ℕ}, @ext Γ Γ n id = id
    | Γ n := funext ext_identity

    /-- Composing extensions is equivalent extending a composition. -/
    lemma ext_with_compose :
      ∀ {Γ Δ η} {n : ℕ}
        (P : level (context.extend n Γ) → Prop)
        (ρ : Π (x : name Γ), P (level.extend (name.to_level x)) → name Δ)
        (σ : name Δ → name η)
        (a : name (context.extend n Γ)) (p : P (name.to_level a))
      , ext σ (ext_with P ρ a p) = ext_with P (λ a p, σ (ρ a p)) a p
    | Γ Δ η n P ρ σ (zero lt) _ := rfl
    | Γ Δ η n P ρ σ (extend a) _ := rfl

    /-- Composing extensions is equivalent extending a composition. -/
    lemma ext_with_comp {Γ Δ η} {n : ℕ}
        (P : level (context.extend n Γ) → Prop)
        (ρ : Π (x : name Γ), P (level.extend (name.to_level x)) → name Δ)
        (σ : name Δ → name η)
      : (λ a p, ext σ (ext_with P ρ a p)) = ext_with P (λ a p, σ (ρ a p))
      := funext $ λ a, funext (ext_with_compose P ρ σ a)

    /-- Composing extensions is equivalent extending a composition. -/
    lemma ext_compose {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η) {n : ℕ}
      (a : name (context.extend n Γ))
      : ext σ (ext ρ a) = ext (σ ∘ ρ) a
      := ext_with_compose (λ _, true) (λ x _, ρ x) σ a true.intro

    /-- Composing extensions is equivalent extending a composition. -/
    lemma ext_comp {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η) {n : ℕ}
      : (ext σ ∘ ext ρ) = @ext _ _ n (σ ∘ ρ)
      := funext (ext_compose ρ σ)

    /-- Extending then renaming with an extended function, is equivalent to
        renaming then extending. -/
    lemma ext_extend {Γ Δ} {n : ℕ} (ρ : name Γ → name Δ)
      : (ext ρ ∘ extend) = (@extend Δ n ∘ ρ)
      := funext (λ x, rfl)

    /-- Rewrite one ext_with to another -/
    lemma ext_with_discard {Γ Δ} {n}
        (P : level (context.extend n Γ) → Prop)
        (ρ : name Γ → name Δ)
      : (ext_with P (λ a _, ρ a))
      = (λ a _, name.ext_with (λ _x, true) (λ x _, ρ x) a true.intro)
      := funext $ λ a, funext $ λ free, by { cases a; unfold ext_with }

    /-- Swap the two topmost variables. Used for exchange of ν terms. -/
    def swap {Γ} {M N : ℕ}
      : name (context.extend M (context.extend N Γ))
      → name (context.extend N (context.extend M Γ))
    | (zero lt) := extend (zero lt)
    | (extend (zero lt)) := zero lt
    | (extend (extend n)) := extend (extend n)

    /-- A twice-extended renaming function can be applied before or after a swap.
    -/
    lemma swap_ext_ext {Γ Δ} {ρ : name Γ → name Δ} {m n : ℕ}
      : (ext (ext ρ) ∘ swap)
      = (swap ∘ @ext _ _ n (@ext _ _ m ρ)) := funext $ λ α,
        match α with
        | zero p := by simp [swap, ext, ext_with]
        | extend (zero lt) := by simp [swap, ext, ext_with]
        | extend (extend _) := by simp [swap, ext, ext_with]
        end

    /-- Incrementing and swapping, is just the same as incrementing everything
        above 0. -/
    lemma swap_comp_extend {Γ} {m n : ℕ}
      : (@name.swap Γ m n ∘ name.extend) = (name.ext name.extend) := funext $ λ α,
        match α with
        | zero idx := by simp [swap, ext, ext_with]
        | extend n := by simp [swap, ext, ext_with]
        end

    /-- Incrementing everything above 0 and swapping is the same as just
        incrementing above 0. -/
    lemma swap_comp_ext_extend {Γ} {m n : ℕ}
      : (@name.swap Γ m n ∘ name.ext name.extend) = name.extend := funext $ λ α,
        match α with
        | zero idx := by simp [swap, ext, ext_with]
        | extend n := by simp [swap, ext, ext_with]
        end
  end rename

end name

end cpi

#sanity_check
