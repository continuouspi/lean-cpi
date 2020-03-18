import data.fin_fn

/-- A multi-variate, computable polynomial. Based off mathlib's mv_polynomial
    definition. -/
@[nolint has_inhabited_instance]
def fin_poly (α : Type*) (β : Type*) [has_zero β] := fin_fn (fin_fn α ℕ) β

section instances
  variables (α : Type*) (β : Type*) [decidable_eq α] [decidable_eq β]

  instance [add_comm_group β] : add_comm_group (fin_poly α β) := fin_fn.add_comm_group _ β
  instance [has_zero β] : decidable_eq (fin_poly α β) := fin_fn.decidable_eq _ β
  instance [comm_ring β] : monoid (fin_poly α β) :=
    { mul := λ f g, f.sum (λ a₁ b₁, g.sum (λ a₂ b₂, fin_fn.single (a₁ + a₂) (b₁ * b₂))),
      mul_assoc := λ f g h, begin
        unfold has_mul.mul fin_fn.sum,
        sorry,
      end,
      one := fin_fn.single 0 1,
      one_mul := λ g, begin
        have : ∀ a₁, fin_fn.sum g (λ a₂ b₂, fin_fn.single (a₁ + a₂) (0 * b₂)) = 0,
        { assume a, simp only [zero_mul, fin_fn.single_zero, fin_fn.sum_const_zero] },
        sorry,
        -- simp only [fin_fn.sum_single _ _ (λ a₁ b₁, g.sum (λ a₂ b₂, fin_fn.single (a₁ + a₂) (b₁ * b₂))) this, zero_add, one_mul],
      end,
      mul_one := λ g, begin
        unfold has_mul.mul, unfold semigroup.mul,

        have : (λ (a₁ : fin_fn α ℕ) (b₁ : β),
                fin_fn.sum (fin_fn.single 0 1) (λ (a₂ : fin_fn α ℕ) (b₂ : β), fin_fn.single (a₁ + a₂) (b₁ * b₂)))
            = fin_fn.single,
        {
          ext a₁ b₁,
          have this := fin_fn.sum_single_index 0 1 (λ (a₂ : fin_fn α ℕ) (b₂ : β), fin_fn.single (a₁ + a₂) (b₁ * b₂))
            (λ x, by simp only [mul_zero, fin_fn.single_zero]),
          simp only [this, add_zero, mul_one],
        },
        rw this,
      end,
      -- left_distrib := _,
      -- right_distrib := _,
    --   mul_comm := _ ,
    -- .. fin_poly.add_comm_group _ _
    }

end instances

#lint-
