import data.real.basic

/-- A non-negative real number.
-/
def real_non_neg : Type := { val : ℝ // 0 ≤ val }

notation `ℝ≥0` := real_non_neg

def x : real_non_neg := ⟨ 0, le_refl 0 ⟩

namespace real_non_neg
  instance : has_zero ℝ≥0 := ⟨⟨0, le_refl 0⟩⟩
  instance : has_one ℝ≥0 := ⟨⟨1, zero_le_one⟩⟩
  instance : has_add ℝ≥0 := ⟨ λ ⟨ x, px ⟩ ⟨ y, py ⟩,
    ⟨ x + y, zero_add (0 : ℝ) ▸ add_le_add px py ⟩ ⟩
end real_non_neg
