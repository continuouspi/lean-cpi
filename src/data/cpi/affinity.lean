import data.pand data.fin data.fintype data.upair

namespace cpi

/-- An affinity network.

    This is composed of $arity$ names, and a partial function `f' which defines
    the affinities between elements of this matrix.
-/
@[derive decidable_eq, nolint has_inhabited_instance]
structure affinity (ℍ : Type) := intro ::
  (arity : ℕ)
  (f : fin arity → fin arity → option ℍ)
  (symm : ∀ x y, f x y = f y x)

variables {ℍ : Type}

/-- Read a value from an affinity network using an unordered pair. -/
def affinity.get (M : affinity ℍ) : upair (fin M.arity) → option ℍ
| p := upair.lift_on p M.f M.symm

end cpi

#lint-
