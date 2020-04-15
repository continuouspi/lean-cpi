import data.fin data.fintype data.upair

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

instance affinity.has_empty : has_emptyc (affinity ℍ) := ⟨ { arity := 0, f := λ x y, none, symm := λ x y, rfl } ⟩

/-- Make an affinity network with an affinity between two names.. -/
def affinity.mk (arity : ℕ) (a b : fin arity) (c : ℍ) : affinity ℍ :=
  { arity := arity,
    f := λ x y,
      if (x = a ∧ y = b) ∨ (y = a ∧ x = b) then some c
      else none,
    symm := λ x y, begin
      by_cases (x = a ∧ y = b) ∨ (y = a ∧ x = b),
      simp only [if_pos h, if_pos (or.swap h)],
      simp only [if_neg h, if_neg (h ∘ or.swap)],
    end }

/-- Compose two affinity networks together. Applying a, and then b if it does not match. -/
def affinity.compose : ∀ (a b : affinity ℍ), a.arity = b.arity → affinity ℍ
| ⟨ arity, f_a, symm_a ⟩ ⟨ _, f_b, symm_b ⟩ h := begin
  simp only [] at h, subst h, -- using rfl clears symm_b for some reason.
  from
  { arity := arity,
    f := λ x y, f_a x y <|> f_b x y,
    symm := λ x y, by simp only [symm_a, symm_b] }
end

/-- Make an affinity network of arity 2 names and a single affinity between the two. -/
def affinity.mk_pair (c : ℍ) : affinity ℍ := affinity.mk 2 0 1 c

notation a ` ∘[` e `] ` b := affinity.compose a b e
notation a ` ∘[] ` b := affinity.compose a b rfl

end cpi

#lint-
