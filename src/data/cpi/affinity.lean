import data.pand data.fin data.fintype

namespace cpi

/-- An affinity network.

    This is composed of $arity$ names, and a partial function `f' which defines
    the affinities between elements of this matrix.
-/
@[derive decidable_eq]
structure affinity (ℍ : Type) := intro ::
  (arity : ℕ)
  (f : fin arity → fin arity → option ℍ)
  (symm : ∀ x y, f x y = f y x)

variables {ℍ : Type}

end cpi

#lint -
