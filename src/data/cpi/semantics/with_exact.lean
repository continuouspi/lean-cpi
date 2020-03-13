import data.cpi.semantics.space

namespace cpi

namespace exact

variables {ℍ : Type} {ω : context}
def species_setoid {Γ} : setoid (species ℍ ω Γ) := ⟨ eq, eq_equivalence ⟩
def concretion_setoid {b y Γ} : setoid (concretion ℍ ω b y Γ) := ⟨ eq, eq_equivalence ⟩

localized "attribute [instance] cpi.exact.species_setoid cpi.exact.concretion_setoid"
    in exact

instance species.has_repr [has_repr ℍ] {Γ} : has_repr (species' ℍ ω Γ) :=
  ⟨ λ x, quot.lift_on x repr (λ x y eql, by { cases eql, from rfl }) ⟩

instance concretion.has_repr [has_repr ℍ] {b y Γ} : has_repr (concretion' ℍ ω b y Γ) :=
  ⟨ λ x, quot.lift_on x repr (λ x y eql, by { cases eql, from rfl }) ⟩

def prime_decompose {Γ} : species ℍ ω Γ → list (prime_species ℍ ω Γ)
| A :=
  list.map_witness (parallel.to_list A) (λ B mem, ⟨ B,
  λ eql, by { cases eql, from parallel.to_list_nonnil _ mem},
  λ B₁ B₂ eql, by { cases eql, from absurd mem (parallel.to_list_nonparallel _ _ _) } ⟩)

def prime_decompose' {Γ} : species' ℍ ω Γ → multiset (prime_species' ℍ ω Γ)
  := quot.map (λ A, list.map quotient.mk (prime_decompose A))
    (λ x y r, by { cases r, from refl _ })

def cpi_equiv (ℍ : Type) (ω : context) [decidable_eq ℍ] : cpi_equiv ℍ ω :=
  { species_equiv := by apply_instance,
    concretion_equiv := by apply_instance,
    decide_species := by apply_instance,
    decide_concretion := by apply_instance,
    prime_decompose := λ Γ, prime_decompose',
    prime_decompose_nil := λ Γ, sorry,
    prime_decompose_parallel := λ Γ, sorry,
    prime_decompose_prime := λ Γ, sorry,
    pseudo_apply := λ Γ b y F G, quotient.lift_on₂ F G
      (λ F G, ⟦ concretion.pseudo_apply F G ⟧)
      (λ F G F' G' eqF eqG, by { cases eqF, cases eqG, from rfl }) }

localized "attribute [instance] cpi.exact.cpi_equiv" in exact

end exact

end cpi
