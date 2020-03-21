import data.cpi.semantics.relation

namespace cpi

namespace congruence

variables {ℍ : Type} {ω : context}

open_locale congruence
open species.equiv

-- These are fairly obvious from the definition of has_prime_decompose, but
-- thanks to propositional irrelevence it's impossible.
--
-- I guess the alternative would be to make it correct by construction, but
-- that's annoying.
axiom prime_decompose_nil {Γ} : prime_decompose (@nil ℍ ω Γ) = 0
axiom prime_decompose_parallel {Γ} (A B : species ℍ ω Γ) : prime_decompose (A |ₛ B) = prime_decompose A + prime_decompose B
axiom prime_decompose_prime {Γ} (A : prime_species ℍ ω Γ) : prime_decompose A.val = [ A ]
axiom prime_decompose_equiv {Γ} {A B : species ℍ ω Γ}
  : A ≈ B
  → multiset.map quotient.mk (prime_decompose A)
  = multiset.map quotient.mk (prime_decompose B)

noncomputable def cpi_equiv_prop (ℍ : Type) (ω : context) [decidable_eq ℍ] : cpi_equiv_prop ℍ ω :=
  { species_equiv := by apply_instance,
    concretion_equiv := by apply_instance,
    decide_species := λ Γ, classical.dec_rel _,
    decide_concretion := λ Γ b y, classical.dec_rel _,
    prime_decompose := λ Γ, prime_decompose,
    prime_decompose_equiv := λ Γ A B, prime_decompose_equiv,
    prime_decompose_nil := λ Γ, prime_decompose_nil,
    prime_decompose_parallel := λ Γ, prime_decompose_parallel,
    prime_decompose_prime := λ Γ, prime_decompose_prime,
    pseudo_apply := λ Γ b y, concretion.pseudo_apply.quotient,
    transition_iso := λ Γ ℓ A B ⟨ eq ⟩, ⟨ λ k α,
      ⟨ transition.equivalent_of.is_equiv eq, transition.equivalent_of.map_equiv eq ⟩ ⟩,
    pseudo_apply_symm := λ Γ b y, concretion.pseudo_apply.quotient.symm }

localized "attribute [instance] cpi.congruence.cpi_equiv_prop" in congruence

end congruence

end cpi
