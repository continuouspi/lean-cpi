/- The definition of environments, contexts and names within the continuous-π
   calculus.

   Names are represented as de Bruijn indicies for obvious reasons. We use the
   same representation of names as [1], indexing them by the context that they
   exist in. This ensures that names are always well formed, thus avoiding many
   common pitfalls that occur when renaming and shuffling terms.

   We have two tiers of contexts and names which, while structurally quite
   similar, have rather different purposes.

    - Environment and references: The environment acts as a store for the
      definitions of species. Invocations D(a̅) reference into this table.

      Each reference within this environment is given an arity, holding the
      arity of its corresponding definition.

      Unlike contexts, the environment should remain constant across a whole
      series of processes.

   - Contexts hold names on the π-calculus level, either those in the global
     affinity network or locally bound names introduced by restrictions.

     Like with environments, each context defines the arity of the affinity
     network introduced at that level. Names then index into that affinity
     network, using finite number bounded by the arity.

  [1]: Proof-relevant π-calculus: a constructive account of concurrency and
       causality, Roly Perera, James Cheney
-/
import tactic.sanity_check data.fin

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi

/-- A environment under which species definitions will be looked up.

    Each level of the environment holds the arity of the species defined at that
    point. -/
@[derive decidable_eq]
inductive environment
| nil : environment
| extend : ℕ → environment → environment

/-- A reference to a species definition within an environment. -/
@[derive decidable_eq]
inductive reference : environment → Type
| zero   {ω : environment} {n : ℕ} : reference (environment.extend n ω)
| extend {ω : environment} {n : ℕ} : reference ω → reference (environment.extend n ω)

/-- A context under which terms may be evaluated.

    Each level of the context holds the arity of the vector defined at that
    point. -/
@[derive decidable_eq]
inductive context : environment → Type
| nil (ω : environment) : context ω
| extend {ω : environment} : ℕ → context ω → context ω

variable {ω : environment}

/-- The set of names within the continuous-π calculus. -/
@[derive decidable_eq]
inductive name : context ω → Type
| zero   {Γ} {n : ℕ} : fin n → name (context.extend n Γ)
| extend {Γ} {n : ℕ} : name Γ → name (context.extend n Γ)

/-- The "depth" of a variable.

    This is effectively a name, but without the index into the affinity network.
    It is used to determine if the affinity network appears at all within a
    term.

    Technically this property could be defined as "does any name of this level
    appear" - it may be worth seeing if that simplifies things in the future. -/
@[derive decidable_eq]
inductive level : context ω → Type
| zero   {Γ} {n} : level (context.extend n Γ)
| extend {Γ} {n} : level Γ → level (context.extend n Γ)

namespace name
  def to_level : ∀ {Γ : context ω}, name Γ → level Γ
  | ._ (zero _) := level.zero
  | ._ (extend a) := level.extend (to_level a)

  /- Just show that names form a decidable linear order. -/
  section ordering
    inductive le : ∀ {Γ : context ω}, name Γ → name Γ → Prop
    | zero {Γ} {n} {i j : fin n} :    i ≤ j → le (@zero _ Γ n i) (zero j)
    | one  {Γ} {n} {i : fin n} (a : name Γ) : le (@zero _ Γ n i) (extend a)
    | succ {Γ} {n} {a b : name Γ} :  le a b → le (@extend _ Γ n a) (extend b)

    protected theorem le_refl : ∀ {Γ : context ω} (α : name Γ), name.le α α
    | ._ (zero x) := le.zero (nat.le_refl x.val)
    | ._ (extend x) := le.succ (le_refl x)

    protected theorem le_trans :
      ∀ {Γ : context ω} (a b c : name Γ), name.le a b → name.le b c → name.le a c
    | ._ ._ ._ ._ (le.zero ab) (le.zero bc) := le.zero (preorder.le_trans _ _ _ ab bc)
    | ._ ._ ._ ._ (le.zero ab) (le.one c) := le.one c
    | ._ ._ ._ ._ (le.succ ab) (le.succ bc) := le.succ (le_trans _ _ _ ab bc)
    | ._ ._ ._ ._ (le.one β') (le.succ _) := le.one _

    protected theorem le_antisymm :
      ∀ {Γ : context ω} (a b : name Γ), le a b → le b a → a = b
    | ._ (zero a) (zero b) (le.zero ab) (le.zero ba) := by rw partial_order.le_antisymm _ _ ab ba
    | ._ (extend a) (extend b) (le.succ ab) (le.succ ba) := by rw le_antisymm a b ab ba

    protected theorem le_total : ∀ {Γ : context ω} (a b : name Γ), le a b ∨ le b a
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

    protected def decidable_le : ∀ {Γ : context ω} (a b : name Γ), decidable (le a b)
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

    instance {Γ : context ω} : decidable_linear_order (name Γ) :=
      { le := name.le,
        le_refl := name.le_refl,
        le_trans := name.le_trans,
        le_antisymm := name.le_antisymm,
        le_total := name.le_total,
        decidable_le := name.decidable_le,
        decidable_eq := by apply_instance }
  end ordering

  section free
    /-- Determine if this variable is on a specific level or depth.

        This can be thought of as a determining if a given level is free within
        this variable. -/
    def at_level : ∀ {Γ : context ω}, level Γ → name Γ → Prop
    | ._ level.zero (zero _) := true
    | ._ (level.extend l) (extend a) := at_level l a

    | ._ level.zero (extend _) := false
    | ._ (level.extend _) (zero _) := false

    instance {Γ : context ω} : has_mem (level Γ) (name Γ) := ⟨ at_level ⟩

    private def at_level_decide :
      ∀ {Γ : context ω} (l : level Γ) (a : name Γ), decidable (at_level l a)
    | ._ level.zero (zero _) := decidable.true
    | ._ (level.extend l) (extend a) := begin
        unfold at_level,
        from at_level_decide l a
      end
    | ._ level.zero (extend _) := decidable.false
    | ._ (level.extend _) (zero _) := decidable.false

    instance at_level.decidable {Γ : context ω} {l} {a : name Γ} : decidable (at_level l a)
      := at_level_decide l a

    /-- Any variable is always at the level provided by to_level. -/
    theorem to_level_at : ∀ {Γ : context ω} (a : name Γ), name.to_level a ∈ a
    | ._ (zero _) := by unfold to_level
    | ._ (extend n) := to_level_at n
  end free

  /- Renaming applies a function to all variables in the current context,
     mapping them to a new set of variables in a different (or the same)
     context.

     Our renaming code is pretty typical, though with some additional
     complexities. The actual renaming function receives evidence that the
     provided variable is used (typically, that it is free within the term
     begin renamed).

     While this may seem like an obvious fact, it is crucial to allow lowering
     the level of names - if we know `name.zero ∉ A', then we can safely reduce
     all variables by one, as we can show by contradiction that our renaming
     function doesn't receive `name.zero'.

     Any functions suffixed with `_with' use this more complex definition of
     renaming - we also provide simpler ones which provide a simple
     `name Γ → name Δ' interface (and a few additional guarantees). -/
  section rename
    /-- Wrap a renaming function, making it suitable for a nested context. -/
    def ext_with {Γ Δ : context ω} {n}
        (P : level (context.extend n Γ) → Prop)
        (ρ : Π (x : name Γ), P (level.extend (name.to_level x)) → name Δ)
      : Π (x : name (context.extend n Γ)), P (name.to_level x) → name (context.extend n Δ)
    | (zero idx) p := zero idx
    | (extend a) p := extend (ρ a p)

    /-- Extending with `id' does nothing. -/
    lemma ext_with_identity :
      ∀ {Γ  : context ω} {n : ℕ}
        (P : level (context.extend n Γ) → Prop)
        (a : name (context.extend n Γ)) (p : P (name.to_level a))
      , ext_with P (λ x _, x) a p = a
    | Γ n P (zero lt) _ := rfl
    | Γ n P (extend a) _ := rfl

    /-- Extending with `id' is equivalent to the identity function. -/
    lemma ext_with_id {Γ : context ω} {n : ℕ}
        (P : level (context.extend n Γ) → Prop)
      : ext_with P (λ x _, x) = λ x _, x
      := funext $ λ a, funext (ext_with_identity P a)

    /-- Wrap a simple renaming function, making it suitable for a nested
        context. -/
    @[reducible]
    def ext {Γ Δ : context ω} {n} (ρ : name Γ → name Δ)
          : name (context.extend n Γ) → name (context.extend n Δ)
    | a := ext_with (λ _, true) (λ x p, ρ x) a true.intro

    /-- Extending with the identity does nothing. -/
    lemma ext_identity {Γ : context ω} {n : ℕ} (a : name (context.extend n Γ))
      : ext id a = a
      := ext_with_identity _ a _

    /-- Extending with `id' is equivalent to the identity function. -/
    lemma ext_id : ∀ {Γ : context ω} {n : ℕ}, @ext _ Γ Γ n id = id
    | Γ n := funext ext_identity

    /-- Composing extensions is equivalent extending a composition. -/
    lemma ext_with_compose :
      ∀ {Γ Δ η : context ω} {n : ℕ}
        (P : level (context.extend n Γ) → Prop)
        (ρ : Π (x : name Γ), P (level.extend (name.to_level x)) → name Δ)
        (σ : name Δ → name η)
        (a : name (context.extend n Γ)) (p : P (name.to_level a))
      , ext σ (ext_with P ρ a p) = ext_with P (λ a p, σ (ρ a p)) a p
    | Γ Δ η n P ρ σ (zero lt) _ := rfl
    | Γ Δ η n P ρ σ (extend a) _ := rfl

    /-- Composing extensions is equivalent extending a composition. -/
    lemma ext_with_comp {Γ Δ η : context ω} {n : ℕ}
        (P : level (context.extend n Γ) → Prop)
        (ρ : Π (x : name Γ), P (level.extend (name.to_level x)) → name Δ)
        (σ : name Δ → name η)
      : (λ a p, ext σ (ext_with P ρ a p)) = ext_with P (λ a p, σ (ρ a p))
      := funext $ λ a, funext (ext_with_compose P ρ σ a)

    /-- Composing simple extensions is equivalent extending a composition. -/
    lemma ext_compose {Γ Δ η : context ω} (ρ : name Γ → name Δ) (σ : name Δ → name η) {n : ℕ}
      (a : name (context.extend n Γ))
      : ext σ (ext ρ a) = ext (σ ∘ ρ) a
      := ext_with_compose (λ _, true) (λ x _, ρ x) σ a true.intro

    /-- Composing simple extensions is equivalent extending a composition. -/
    lemma ext_comp {Γ Δ η : context ω} (ρ : name Γ → name Δ) (σ : name Δ → name η) {n : ℕ}
      : (ext σ ∘ ext ρ) = @ext _ _ _ n (σ ∘ ρ)
      := funext (ext_compose ρ σ)

    /-- Extending then renaming with an extended function, is equivalent to
        renaming then extending. -/
    lemma ext_extend {Γ Δ : context ω} {n : ℕ} (ρ : name Γ → name Δ)
      : (ext ρ ∘ extend) = (@extend _ Δ n ∘ ρ)
      := funext (λ x, rfl)

    /-- Rewrite one ext_with to another.

        This is largely useful when proving renaming properties in more complex
        types. -/
    lemma ext_with_discard {Γ Δ : context ω} {n}
        (P : level (context.extend n Γ) → Prop)
        (ρ : name Γ → name Δ)
      : (ext_with P (λ a _, ρ a))
      = (λ a _, name.ext_with (λ _x, true) (λ x _, ρ x) a true.intro)
      := funext $ λ a, funext $ λ free, by { cases a; from rfl }
  end rename

  section swap
    /-- Swap the two topmost variables. Used for exchange of ν(_) terms. -/
    def swap {Γ : context ω} {M N : ℕ}
      : name (context.extend M (context.extend N Γ))
      → name (context.extend N (context.extend M Γ))
    | (zero lt) := extend (zero lt)
    | (extend (zero lt)) := zero lt
    | (extend (extend n)) := extend (extend n)

    /-- A twice-extended renaming function can be applied before or after a
        swap. -/
    lemma swap_ext_ext {Γ Δ : context ω} {ρ : name Γ → name Δ} {m n : ℕ}
      : (ext (ext ρ) ∘ swap)
      = (swap ∘ @ext _ _ _ n (@ext _ _ _ m ρ)) := funext $ λ α,
        match α with
        | zero p := rfl
        | extend (zero lt) := rfl
        | extend (extend _) := rfl
        end

    /-- Incrementing names and swapping, is just the same as incrementing
        everything above 0. -/
    lemma swap_comp_extend {Γ : context ω} {m n : ℕ}
      : (@name.swap _ Γ m n ∘ name.extend) = (name.ext name.extend)
      := funext $ by { assume a, cases a; from rfl }

    /-- Incrementing all names above 0 and swapping is the same as just
        incrementing everything. -/
    lemma swap_comp_ext_extend {Γ : context ω} {m n : ℕ}
      : (@name.swap _ Γ m n ∘ name.ext name.extend) = name.extend
      := funext $ by { assume a, cases a; from rfl }
  end swap
end name

end cpi

#sanity_check
