import data.cpi.species data.cpi.process.basic

namespace cpi
namespace process

variables {ℂ ℍ : Type} {ω Γ : context} [has_add ℂ] [∀ Γ, setoid (species ℍ ω Γ)]

/-- Structural congruence of processes. -/
inductive equiv : process ℂ ℍ ω Γ → process ℂ ℍ ω Γ → Prop
| refl  {A}     : equiv A A
| trans {A B C} : equiv A B → equiv B C → equiv A C
| symm  {A B}   : equiv A B → equiv B A

-- Projection
| ξ_species   {c : ℂ} {A B} : A ≈ B → equiv (c ◯ A) (c ◯ B)
| ξ_parallel₁ {P P' Q} : equiv P P' → equiv (P |ₚ Q) (P' |ₚ Q)
| ξ_parallel₂ {P Q Q'} : equiv Q Q' → equiv (P |ₚ Q) (P |ₚ Q')

-- Monoidic properties
| parallel_nil   {P} {c : ℂ} : equiv (P |ₚ c ◯ species.nil) P
| parallel_symm  {P Q} : equiv (P |ₚ Q) (Q |ₚ P)
| parallel_assoc {P Q R} : equiv ((P |ₚ Q) |ₚ R) (P |ₚ (Q |ₚ R))

-- Join identical species together.
| join  {A} {c d} : equiv (c ◯ A |ₚ d ◯ A) ((c + d) ◯ A)
| split {A B} {c : ℂ} : equiv (c ◯ (A |ₛ B)) (c ◯ A |ₚ c ◯ B)

instance : is_equiv (process ℂ ℍ ω Γ) equiv :=
  { refl := @equiv.refl _ _ _ _ _ _, symm := @equiv.symm _ _ _ _ _ _, trans := @equiv.trans _ _ _ _ _ _ }
instance : is_refl (process ℂ ℍ ω Γ) equiv := ⟨ λ _, equiv.refl ⟩
instance : setoid (process ℂ ℍ ω Γ) :=
  ⟨ equiv, ⟨ @equiv.refl _ _ _ _ _ _, @equiv.symm _ _ _ _ _ _, @equiv.trans _ _ _ _ _ _ ⟩ ⟩
instance setoid.is_equiv : is_equiv (process ℂ ℍ ω Γ) has_equiv.equiv :=
  process.is_equiv

namespace equiv
  lemma parallel_symm₁ {P Q R : process ℂ ℍ ω Γ} : (P |ₚ Q |ₚ R) ≈ (Q |ₚ P |ₚ R) :=
    calc  (P |ₚ (Q |ₚ R))
        ≈ ((P |ₚ Q) |ₚ R) : symm parallel_assoc
    ... ≈ ((Q |ₚ P) |ₚ R) : ξ_parallel₁ parallel_symm
    ... ≈ (Q |ₚ (P |ₚ R)) : parallel_assoc

  lemma parallel_symm₂ {P Q R : process ℂ ℍ ω Γ} : ((P |ₚ Q) |ₚ R) ≈ ((P |ₚ R) |ₚ Q) :=
    calc  ((P |ₚ Q) |ₚ R)
        ≈ (P |ₚ (Q |ₚ R)) : parallel_assoc
    ... ≈ (P |ₚ (R |ₚ Q)) : ξ_parallel₂ parallel_symm
    ... ≈ ((P |ₚ R) |ₚ Q) : symm parallel_assoc
end equiv

namespace parallel.quot
  /-- Make a parallel process from a quotient of two process. -/
  def mk : quotient (@process.setoid ℂ ℍ ω Γ _ _) → quotient (@process.setoid ℂ ℍ ω Γ _ _) → quotient (@process.setoid ℂ ℍ ω Γ _ _)
  | A B := quotient.lift_on₂ A B (λ A B, ⟦ A |ₚ B ⟧)
      (λ A B A' B' eqA eqB, quot.sound (trans (equiv.ξ_parallel₁ eqA) ((equiv.ξ_parallel₂ eqB))))

  lemma assoc (A B C : quotient (@process.setoid ℂ ℍ ω Γ _ _))
    : mk A (mk B C) = mk (mk A B) C
    := begin
      rcases quot.exists_rep A with ⟨ A, ⟨ _ ⟩ ⟩,
      rcases quot.exists_rep B with ⟨ B, ⟨ _ ⟩ ⟩,
      rcases quot.exists_rep C with ⟨ C, ⟨ _ ⟩ ⟩,
      from quot.sound (symm equiv.parallel_assoc),
    end
end parallel.quot

end process

/-- A quotient of all structurally congruent processes. -/
@[nolint has_inhabited_instance]
def process' (ℂ ℍ : Type) (ω Γ : context) [has_add ℂ] [∀ {Γ}, setoid (species ℍ ω Γ)]
  := quotient (@process.setoid ℂ ℍ ω Γ _ _)

section prime
  variables {ℂ ℍ : Type} {ω Γ : context} [∀ Γ, setoid (species ℍ ω Γ)]

  /-- Convert a list of prime species into a process-/
  def process.from_primes [add_monoid ℂ] {Γ} (f : prime_species' ℍ ω Γ → ℂ)
    : list (prime_species' ℍ ω Γ) → process' ℂ ℍ ω Γ
  | [] := ⟦ 0 ◯ nil ⟧
  | (A :: As) :=
    let A' := quot.lift_on A (λ B, ⟦ f A ◯ B.val ⟧)
                (λ A B r, quot.sound (process.equiv.ξ_species r))
    in process.parallel.quot.mk A' (process.from_primes As)

  /-- Convert a multiset of prime species into a process. -/
  def process.from_prime_multiset [add_monoid ℂ] {Γ} (f : prime_species' ℍ ω Γ → ℂ)
    : multiset (prime_species' ℍ ω Γ) → process' ℂ ℍ ω Γ
  | Ps := quot.lift_on Ps (process.from_primes f) (λ P Q r, begin
    induction r,
    case list.perm.nil { from rfl },
    case list.perm.trans : A B C _ _ ab bc { from trans ab bc },
    case list.perm.skip : A As Bs _ ih { simp only [process.from_primes, ih] },
    case list.perm.swap : A B As {
      simp only [process.from_primes],
      rcases quot.exists_rep A with ⟨ A, eq ⟩, subst eq,
      rcases quot.exists_rep B with ⟨ B, eq ⟩, subst eq,
      rcases quot.exists_rep (process.from_primes f As) with ⟨ As, eq ⟩, rw ← eq, clear eq,
      from quot.sound process.equiv.parallel_symm₁,
    },
  end)
end prime
end cpi

#lint-
