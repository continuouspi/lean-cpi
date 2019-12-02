import data.cpi.semantics.basic data.mv_polynomial

namespace cpi

variables {ℍ : Type} {ω : context} [half_ring ℍ] [decidable_eq ℍ]
local attribute [instance] prime_equal concretion_equal

/-- All species which may occur within the transition graph of a process.

    As the transition graph may be infinite, we visit the graph with a finite
    amount of gas. If we run out of gas, we return an incomplete set, otherwise
    we return a complete one. -/
inductive all_species
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
    -- (P : process ℍ ω (context.extend M.arity context.nil))
  : Type

| incomplete {}
  : finset (prime_species' ℍ ω (context.extend M.arity context.nil))
  → all_species

| complete :
  ∀ (As : finset (prime_species' ℍ ω (context.extend M.arity context.nil)))
  , (process_immediate.quot M ℓ (process.from_prime_multiset (λ _, 1) As.val)).defined ⊆ As
  → all_species

/-- Get all species in the transition graph for a finset of prime species. -/
noncomputable def all_species.finset (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
  : ℕ → finset (prime_species' ℍ ω (context.extend M.arity context.nil)) → all_species M ℓ
| 0 As := all_species.incomplete As
| (nat.succ n) As :=
  let As' := (process_immediate.quot M ℓ (process.from_prime_multiset (λ _, 1) As.val)).defined in
  if eq : As' ⊆ As then all_species.complete As eq else all_species.finset n (As ∪ As')

/--  Get all species in the transition graph for a process. -/
noncomputable def all_species.process (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
  : ℕ → process ℍ ω (context.extend M.arity context.nil) → all_species M ℓ
| fuel P := all_species.finset M ℓ fuel (process.to_space P).defined

end cpi

#lint-
