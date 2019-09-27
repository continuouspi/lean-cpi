/- Order instances for options.

   Not quite sure why they're not built-in already. -/

import tactic.sanity_check

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

variable {α : Type*}

protected def option.le [has_le α] : option α → option α → Prop
| none _ := true
| (some x) none := false
| (some x) (some y) := x ≤ y

protected theorem option.le_refl [preorder α] : ∀ (a : option α), option.le a a
| none := true.intro
| (some x) := le_refl x

protected theorem option.le_trans [preorder α] :
  ∀ (a b c : option α), option.le a b → option.le b c → option.le a c
| none _ _ _ _ := true.intro
| (some _) none _ x _ := false.elim x
| (some _) (some _) (some _) x y := le_trans x y

instance [preorder α] : preorder (option α)
  := { le := option.le, le_refl := option.le_refl, le_trans := option.le_trans }

protected theorem option.le_antisymm [partial_order α] :
  ∀ (a b : option α), option.le a b → option.le b a → a = b
| none none _ _ := rfl
| (some _) (some _) x y := by { simp, from le_antisymm x y }

instance [partial_order α] : partial_order (option α)
  := { le_antisymm := option.le_antisymm, ..option.preorder }

protected theorem option.le_total [linear_order α] :
  ∀ (a b : option α), option.le a b ∨ option.le b a
| none _ := or.inl true.intro
| (some _) none := or.inr true.intro
| (some x) (some y) := le_total x y

instance [linear_order α] : linear_order (option α)
  := { le_total := option.le_total, ..option.partial_order }

protected def option.decidable_le [has_le α] [dec : decidable_rel ((≤) : α → α → Prop)] :
  ∀ (a b : option α), decidable (option.le a b)
| none _ := decidable.true
| (some _) none := decidable.false
| (some x) (some y) := dec x y

instance [decidable_linear_order α] : decidable_linear_order (option α)
  := { decidable_le := option.decidable_le,
       decidable_eq := option.decidable_eq,
       ..option.linear_order }

#sanity_check
