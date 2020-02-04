import data.cpi.species.normalise

namespace cpi
namespace species
namespace normalise

variables {ℍ : Type} {ω : context}

/-- A species is n(ormalise)-prime if it normalises to itself. -/
def prime {Γ} (A : species ℍ ω Γ) : Prop := (normalise_to A).fst = [A]

/-- For instance, we can show that nil is not prime -/
example (Γ : context) : ¬ (prime (@nil ℍ ω Γ))
| p := by { unfold prime normalise_to at p, contradiction }

end normalise
end species
end cpi

#lint-
