import algebra.ring

universe u

/-- Some comm_ring which has a constant "half", where two halves add to 1. -/
class half_ring (α : Type u) extends comm_ring α :=
  (half : α)
  (one_is_two_halves : 1 = half + half)

@[priority 100]
instance linear_ordered_field.to_half_ring (α : Type u) [linear_ordered_field α] : half_ring α :=
  { half := (1 : α) / 2,
    one_is_two_halves := symm (add_halves 1) }

notation `½` := half_ring.half _

#lint-
