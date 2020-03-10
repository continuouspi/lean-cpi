import data.cpi.semantics.basic data.mv_polynomial

namespace cpi

variables {ℍ : Type} {ω : context} [half_ring ℍ] [cpi_equiv_prop ℍ ω]

/-- All species which may occur within the transition graph of a process.

    As the transition graph may be infinite, we visit the graph with a finite
    amount of gas. If we run out of gas, we return an incomplete set, otherwise
    we return a complete one. -/
@[nolint has_inhabited_instance]
inductive all_species
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
    -- (P : process ℍ ω (context.extend M.arity context.nil))
  : Type

| incomplete {}
  : finset (prime_species' ℍ ω (context.extend M.arity context.nil))
  → all_species

| complete :
  ∀ (As : finset (prime_species' ℍ ω (context.extend M.arity context.nil)))
  , (process_immediate.quot M ℓ (distrib_embedding.refl _) (process.from_prime_multiset (λ _, 1) As.val))
      .defined ⊆ As
  → all_species

/-- Get all species in the transition graph for a finset of prime species. -/
noncomputable def all_species.finset (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
  : ℕ → finset (prime_species' ℍ ω (context.extend M.arity context.nil)) → all_species M ℓ
| 0 As := all_species.incomplete As
| (nat.succ n) As :=
  let As' := (process_immediate.quot M ℓ (distrib_embedding.refl _) (process.from_prime_multiset (λ _, 1) As.val)).defined in
  if eq : As' ⊆ As then all_species.complete As eq else all_species.finset n (As ∪ As')

/--  Get all species in the transition graph for a process. -/
noncomputable def all_species.process (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
  : ℕ → process ℍ ℍ ω (context.extend M.arity context.nil) → all_species M ℓ
| fuel P := all_species.finset M ℓ fuel (process.to_space P).defined

noncomputable instance {σ : Type*} {α : Type*} [half_ring α] : half_ring (mv_polynomial σ α)
  := { half := mv_polynomial.C ½,
       one_is_two_halves := begin
        show mv_polynomial.C 1 = (mv_polynomial.C (½ : α)) + (mv_polynomial.C (½ : α)),
        simp only [mv_polynomial.C_add, half_ring.one_is_two_halves],
       end }

/-- A distributive embedding of some ring into polynomials of that ring. -/
noncomputable def mv_polynomial.add_embed {σ : Type*} {α : Type*} [comm_semiring α] : distrib_embedding α (mv_polynomial σ α) (+) (+)
  := { to_embed := { to_fun := mv_polynomial.C,
                     inj := finsupp.injective_single _ },
  distrib := λ x y, mv_polynomial.C_add }

/-- Get a finite set of species (such as those provided by all_species and
    convert it to an ODE) -/
noncomputable def as_ode (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
  : finset (prime_species' ℍ ω (context.extend M.arity context.nil))
  → process_space (mv_polynomial (prime_species' ℍ ω (context.extend M.arity context.nil)) ℍ) ℍ
      ω (context.extend M.arity context.nil)
| As := process_immediate.quot M ℓ mv_polynomial.add_embed
  (process.from_prime_multiset (λ x, mv_polynomial.X x) As.val)

end cpi

#lint-
