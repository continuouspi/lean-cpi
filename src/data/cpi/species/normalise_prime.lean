import data.cpi.species.normalise data.cpi.species.prime

namespace cpi
namespace species
namespace normalise

variables {ℍ : Type} {ω : context}
open_locale normalise

/-- Two species are "almost equal" if they are equal up to guarded choice.

    We require this definition of equality in order to define primality. Guarded
    choices are always prime, so we do not need to worry about anything inside
    them. -/
inductive almost_equal : ∀ {Γ : context} (A B : species ℍ ω Γ), Prop
| refl {Γ} (A : species ℍ ω Γ) : almost_equal A A
| parallel {Γ} {A A' B B' : species ℍ ω Γ}
  : almost_equal A A' → almost_equal B B'
  → almost_equal (A |ₛ B) (A' |ₛ B')
| restriction {Γ} (M : affinity ℍ) {A A' : species ℍ ω (context.extend M.arity Γ)}
  : almost_equal A A'
  → almost_equal (ν(M) A) (ν(M) A')
| choice {Γ} (As As' : choices ℍ ω Γ)
  : almost_equal (Σ# As) (Σ# As')

/-- Ensure that a list contains a single element which is 'almost_equal' to
    another. -/
inductive almost_equal.list {Γ : context} : list (species ℍ ω Γ) → species ℍ ω Γ → Prop
| mk {A A' : species ℍ ω Γ} : almost_equal A A' → almost_equal.list [A] A'

lemma almost_equal.list.refl {Γ : context} (A : species ℍ ω Γ) : almost_equal.list [A] A
  := almost_equal.list.mk (almost_equal.refl A)

/-- A species is n(ormalise)-prime if it normalises to itself. -/
def prime {Γ} (A : species ℍ ω Γ) : Prop
  := almost_equal.list (normalise_to A).fst A

/-- For instance, we can show that nil is not prime -/
example (Γ : context) : ¬ (prime (@nil ℍ ω Γ))
| p := by { unfold prime normalise_to at p, cases p }

/-- Determine if normalising a species or choice yields a list of primes. Note
    that choices are inherently prime. -/
def yields_prime : ∀ {k} {Γ}, whole ℍ ω k Γ → Prop
| kind.species Γ A := ∀ C ∈ (normalise_to A).fst, prime C
| kind.choices Γ A := true

/-- Show that normalisation yields a list of prime species. -/
axiom normalise_prime :
  ∀ {k} {Γ} (A : whole ℍ ω k Γ), yields_prime A

lemma normalise_nil {Γ} : normalise (@nil ℍ ω Γ) = nil
  := by unfold normalise normalise_to parallel.from_list

/-- Show that our reduced definition of primes shows the full definition of
    primes. -/
axiom implies_prime : ∀ {Γ} (A : species ℍ ω Γ), prime A → species.prime A

end normalise

end species
end cpi

#lint-
