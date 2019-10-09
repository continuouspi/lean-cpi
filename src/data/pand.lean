import tactic.sanity_check

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

structure pand {α : Prop} (β : α → Prop) : Prop :=
  mk :: (fst : α) (snd : β fst)

notation `Σ∧` binders `, ` r:(scoped p, pand p) := r

#sanity_check
