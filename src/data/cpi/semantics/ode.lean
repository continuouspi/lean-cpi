import data.cpi.semantics.basic data.fin_poly

namespace cpi

variables {ℍ : Type} {ω : context} [half_ring ℍ] [cpi_equiv_prop ℍ ω] [decidable_eq ℍ]

/-- All species which may occur within the transition graph of a process.

    As the transition graph may be infinite, we visit the graph with a finite
    amount of gas. If we run out of gas, we return an incomplete set, otherwise
    we return a complete one. -/
@[nolint has_inhabited_instance]
inductive all_species (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil)) : Type

| incomplete {}
  : finset (prime_species' ℍ ω (context.extend M.arity context.nil))
  → all_species

| complete :
  ∀ (As : finset (prime_species' ℍ ω (context.extend M.arity context.nil)))
  , (process_immediate.quot M ℓ fin_poly.C.embed (process.from_prime_multiset fin_poly.X As.val))
      .support ⊆ As
  → all_species

/-- Get all species in the transition graph for a finset of prime species. -/
def all_species.finset (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
  : ℕ → finset (prime_species' ℍ ω (context.extend M.arity context.nil)) → all_species M ℓ
| 0 As := all_species.incomplete As
| (nat.succ n) As :=
  let As' := (process_immediate.quot M ℓ fin_poly.C.embed
                (process.from_prime_multiset fin_poly.X As.val)).support in
  if eq : As' ⊆ As then all_species.complete As eq
  else all_species.finset n (As ∪ As')

/--  Get all species in the transition graph for a process. -/
def all_species.process (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
  : ℕ → process ℍ ℍ ω (context.extend M.arity context.nil) → all_species M ℓ
| fuel P := all_species.finset M ℓ fuel (process.to_space P).support

/-- Get a finite set of species (such as those provided by all_species and
    convert it to an ODE) -/
def as_ode (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
  : finset (prime_species' ℍ ω (context.extend M.arity context.nil))
  → process_space
      (fin_poly (prime_species' ℍ ω (context.extend M.arity context.nil)) ℍ)
      ℍ ω (context.extend M.arity context.nil)
| As := process_immediate.quot M ℓ fin_poly.C.embed
  (process.from_prime_multiset (λ x, fin_poly.X x) As.val)

end cpi

#lint-
