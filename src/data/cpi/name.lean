/- The definition of environments, contexts and names within the continuous-π
   calculus.

   Names are represented as de Bruijn indicies for obvious reasons. We use the
   same representation of names as [1], indexing them by the context that they
   exist in. This ensures that names are always well formed, thus avoiding many
   common pitfalls that occur when renaming and shuffling terms.

   We have two kinds of names which, while sharing a context type, do have
   rather different meanings:

    - References to species definitions: The context here acts as a global
      environment `ω', holding the definitions of species. Species invocations
      `D(a̅)' index into this table.

      Each reference within this environment is given an arity, holding the
      arity of its corresponding definition.

      Unlike other contexts, the environment should remain constant across a
      whole series of processes.

   - Names exist on the main π-calculus level, either introduced by the global
     affinity network or locall bound by restrictions.

     Each name also has an arity, representing the arity of the corresponding
     affinity network. Names then index into that affinity network, using finite
     number bounded by the arity.

  [1]: Proof-relevant π-calculus: a constructive account of concurrency and
       causality, Roly Perera, James Cheney
-/
import tactic.lint data.fin data.vector data.vector2

run_cmd lint
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi

/-- A context under which terms may be evaluated and names resolved.

    Each level of the context holds the arity of the name defined at that point.
-/
@[derive decidable_eq]
inductive context : Type
| nil : context
| extend : ℕ → context → context

/-- A reference to a species definition within the global definition context. -/
@[derive decidable_eq]
inductive reference : ℕ → context → Type
| zero   {ω : context} (n : ℕ) : reference n (context.extend n ω)
| extend {ω : context} {n m : ℕ} : reference n ω → reference n (context.extend m ω)

/-- The set of names within the continuous π-calculus. -/
@[derive decidable_eq]
inductive name : context → Type
| zero   {Γ} {n : ℕ} : fin n → name (context.extend n Γ)
| extend {Γ} {n : ℕ} : name Γ → name (context.extend n Γ)

/-- The "depth" of a variable.

    This is effectively a name, but without the index into the affinity network.
    It is used to determine if the affinity network appears at all within a
    term.

    Technically this property could be defined as "does any name of this level
    appear" - it may be worth seeing if that simplifies things in the future. -/
@[derive decidable_eq]
inductive level : context → Type
| zero   {Γ} {n} : level (context.extend n Γ)
| extend {Γ} {n} : level Γ → level (context.extend n Γ)

namespace reference
  /- Just show that names form a decidable linear order. -/
  section ordering
    inductive le : ∀ {ω} {n}, reference n ω → reference n ω → Prop
    | zero {ω} (n) : le (@zero ω n) (@zero ω n)
    | one  {ω} {n} (a : reference n ω) : le (@zero ω n) (extend a)
    | succ {ω} {n m} {a b : reference n ω} : le a b → le (@extend ω n m a) (extend b)

    protected theorem le_refl {n} : ∀ {ω} (α : reference n ω), reference.le α α
    | ._ (zero x) := le.zero x
    | ._ (extend x) := le.succ (le_refl x)

    protected theorem le_trans {n} :
      ∀ {ω} (a b c : reference n ω), reference.le a b → reference.le b c → reference.le a c
    | ._ ._ ._ ._ (le.zero n) (le.zero _) := le.zero n
    | ._ ._ ._ ._ (le.zero n) (le.one c) := le.one c
    | ._ ._ ._ ._ (le.succ ab) (le.succ bc) := le.succ (le_trans _ _ _ ab bc)
    | ._ ._ ._ ._ (le.one β') (le.succ _) := le.one _

    protected theorem le_antisymm {n} :
      ∀ {ω} (a b : reference n ω), le a b → le b a → a = b
    | ._ (zero a) (zero b) (le.zero n) (le.zero _) := rfl
    | ._ (extend a) (extend b) (le.succ ab) (le.succ ba) := by rw le_antisymm a b ab ba

    protected theorem le_total {n} : ∀ {ω} (a b : reference n ω), le a b ∨ le b a
    | ._ (zero n) (zero _) := or.inl (le.zero n)
    | ._ (extend a) (extend b) := or.imp le.succ le.succ (le_total a b)
    | ._ (zero _) (extend _) := or.inl (le.one _)
    | ._ (extend _) (zero _) := or.inr (le.one _)

    protected def decidable_le {n} : ∀ {ω} (a b : reference n ω), decidable (le a b)
    | ._ (zero n) (zero _) := is_true (le.zero n)
    | ._ (zero i) (extend a) := is_true (le.one _)
    | ._ (extend a) (zero i) := is_false (λ x, by cases x)
    | ._ (extend a) (extend b) :=
      match decidable_le a b with
      | is_true h := is_true (le.succ h)
      | is_false h := is_false (λ x, by { clear _match, cases x, contradiction })
      end

    instance {ω} {n} : decidable_linear_order (reference n ω) :=
      { le := reference.le,
        le_refl := reference.le_refl,
        le_trans := reference.le_trans,
        le_antisymm := reference.le_antisymm,
        le_total := reference.le_total,
        decidable_le := reference.decidable_le,
        decidable_eq := by apply_instance }
  end ordering

end reference

namespace name
  def to_level : ∀ {Γ}, name Γ → level Γ
  | ._ (zero _) := level.zero
  | ._ (extend a) := level.extend (to_level a)

  /- Just show that names form a decidable linear order. -/
  section ordering
    inductive le : ∀ {Γ}, name Γ → name Γ → Prop
    | zero {Γ} {n} {i j : fin n} :    i ≤ j → le (@zero Γ n i) (zero j)
    | one  {Γ} {n} {i : fin n} (a : name Γ) : le (@zero Γ n i) (extend a)
    | succ {Γ} {n} {a b : name Γ} :  le a b → le (@extend Γ n a) (extend b)

    protected theorem le_refl : ∀ {Γ} (α : name Γ), name.le α α
    | ._ (zero x) := le.zero (nat.le_refl x.val)
    | ._ (extend x) := le.succ (le_refl x)

    protected theorem le_trans :
      ∀ {Γ} (a b c : name Γ), name.le a b → name.le b c → name.le a c
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
    | ._ (name.extend a) (name.extend b) := or.imp le.succ le.succ (le_total a b)
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
    /-- Determine if this variable is on a specific level or depth.

        This can be thought of as a determining if a given level is free within
        this variable. -/
    def at_level : ∀ {Γ}, level Γ → name Γ → Prop
    | ._ level.zero (zero _) := true
    | ._ (level.extend l) (extend a) := at_level l a

    | ._ level.zero (extend _) := false
    | ._ (level.extend _) (zero _) := false

    instance {Γ} : has_mem (level Γ) (name Γ) := ⟨ at_level ⟩

    private def at_level_decide :
      ∀ {Γ} (l : level Γ) (a : name Γ), decidable (at_level l a)
    | ._ level.zero (zero _) := decidable.true
    | ._ (level.extend l) (extend a) := at_level_decide l a
    | ._ level.zero (extend _) := decidable.false
    | ._ (level.extend _) (zero _) := decidable.false

    instance at_level.decidable {Γ} {l} {a : name Γ} : decidable (at_level l a)
      := at_level_decide l a

    /-- Any variable is always at the level provided by to_level. -/
    theorem to_level_at : ∀ {Γ} (a : name Γ), name.to_level a ∈ a
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
    def ext_with {Γ Δ} {n}
        (P : level (context.extend n Γ) → Prop)
        (ρ : Π (x : name Γ), P (level.extend (name.to_level x)) → name Δ)
      : Π (x : name (context.extend n Γ)), P (name.to_level x) → name (context.extend n Δ)
    | (zero idx) p := zero idx
    | (extend a) p := extend (ρ a p)

    /-- Extending with `id' does nothing. -/
    lemma ext_with_identity :
      ∀ {Γ} {n : ℕ}
        (P : level (context.extend n Γ) → Prop)
        (a : name (context.extend n Γ)) (p : P (name.to_level a))
      , ext_with P (λ x _, x) a p = a
    | Γ n P (zero lt) _ := rfl
    | Γ n P (extend a) _ := rfl

    /-- Extending with `id' is equivalent to the identity function. -/
    lemma ext_with_id {Γ} {n : ℕ} (P : level (context.extend n Γ) → Prop)
      : ext_with P (λ x _, x) = λ x _, x
      := funext $ λ a, funext (ext_with_identity P a)

    /-- Wrap a simple renaming function, making it suitable for a nested
        context. -/
    @[reducible]
    def ext {Γ Δ} {n} (ρ : name Γ → name Δ)
      : name (context.extend n Γ) → name (context.extend n Δ)
    | a := ext_with (λ _, true) (λ x p, ρ x) a true.intro

    /-- Extending with the identity does nothing. -/
    lemma ext_identity {Γ} {n : ℕ} (a : name (context.extend n Γ))
      : ext id a = a
      := ext_with_identity _ a _

    /-- Extending with `id' is equivalent to the identity function. -/
    lemma ext_id : ∀ {Γ} {n : ℕ}, @ext Γ Γ n id = id
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

    /-- Composing simple extensions is equivalent extending a composition. -/
    lemma ext_compose {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η) {n : ℕ}
        (a : name (context.extend n Γ))
      : ext σ (ext ρ a) = ext (σ ∘ ρ) a
      := ext_with_compose (λ _, true) (λ x _, ρ x) σ a true.intro

    /-- Composing simple extensions is equivalent extending a composition. -/
    lemma ext_comp {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η) {n : ℕ}
      : (ext σ ∘ ext ρ) = @ext _ _ n (σ ∘ ρ)
      := funext (ext_compose ρ σ)

    /-- Extending then renaming with an extended function, is equivalent to
        renaming then extending. -/
    lemma ext_extend {Γ Δ} {n : ℕ} (ρ : name Γ → name Δ)
      : (ext ρ ∘ extend) = (@extend Δ n ∘ ρ)
      := funext (λ x, rfl)

    /-- Rewrite one ext_with to another.

        This is largely useful when proving renaming properties in more complex
        types. -/
    lemma ext_with_discard {Γ Δ} {n}
        (P : level (context.extend n Γ) → Prop)
        (ρ : name Γ → name Δ)
      : (ext_with P (λ a _, ρ a))
      = (λ a _, name.ext_with (λ _x, true) (λ x _, ρ x) a true.intro)
      := funext $ λ a, funext $ λ free, by { cases a; from rfl }
  end rename

  section swap
    /-- Swap the two topmost variables. Used for exchange of ν(_) terms. -/
    def swap {Γ} {M N : ℕ}
      : name (context.extend M (context.extend N Γ))
      → name (context.extend N (context.extend M Γ))
    | (zero lt) := extend (zero lt)
    | (extend (zero lt)) := zero lt
    | (extend (extend n)) := extend (extend n)

    /-- A twice-extended renaming function can be applied before or after a
        swap. -/
    lemma swap_ext_ext {Γ Δ} {ρ : name Γ → name Δ} {m n : ℕ}
      : (ext (ext ρ) ∘ swap)
      = (swap ∘ @ext _ _ n (@ext _ _ m ρ))
      := funext $ λ α,
        match α with
        | zero p := rfl
        | extend (zero lt) := rfl
        | extend (extend _) := rfl
        end

    /-- Incrementing names and swapping, is just the same as incrementing
        everything above 0. -/
    lemma swap_comp_extend {Γ} {m n : ℕ}
      : (@name.swap Γ m n ∘ name.extend) = (name.ext name.extend)
      := funext $ λ a, by { cases a; from rfl }

    /-- Incrementing all names above 0 and swapping is the same as just
        incrementing everything. -/
    lemma swap_comp_ext_extend {Γ} {m n : ℕ}
      : (@name.swap Γ m n ∘ name.ext name.extend) = name.extend
      := funext $ λ a, by { cases a; from rfl }

    /-- Swapping twice does nothing. -/
    lemma swap_swap_identity :
      ∀ {Γ} {a b : ℕ} (a : name (context.extend b (context.extend a Γ)))
      , name.swap (name.swap a) = a
      | Γ a b (name.zero _) := rfl
      | Γ a b (name.extend (name.zero _)) := rfl
      | Γ a b (name.extend (name.extend _)) := rfl

    /-- Swapping twice gives the identity. -/
    lemma swap_swap :
      ∀ {Γ} {a b : ℕ}
      , (@name.swap Γ a b) ∘ name.swap = id
      | Γ a b := funext swap_swap_identity
  end swap

  section application
    def mk_apply {Γ} {b} (bs : vector (name Γ) b)
      : name (context.extend b Γ) → name Γ
    | (zero idx) := vector.nth bs idx
    | (extend e) := e

    lemma mk_apply_rename
        {Γ Δ} {b} (ρ : name Γ → name Δ) {bs : vector (name Γ) b}
      : ρ ∘ mk_apply bs = mk_apply (vector.map ρ bs) ∘ name.ext ρ
      := funext $ λ a,
        by { cases a; simp only [mk_apply, ext, ext_with, vector.nth_map, function.comp] }

    lemma mk_apply_ext {Γ} {b} {bs : vector (name Γ) b}
      : mk_apply bs ∘ (@extend Γ b) = id
      := funext $λ α, by { cases α; unfold mk_apply id function.comp }
  end application

  /-- Get the index of a name in the singleton context . -/
  def to_idx {n : ℕ} : name (context.extend n context.nil) → fin n
  | (name.zero i) := i
  | (name.extend a) := by cases a
end name

end cpi

#lint
