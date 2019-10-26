import data.real.nnreal tactic.lint

run_cmd lint
set_option profiler true
set_option profiler.threshold 0.5

notation `ℝ≥0` := nnreal

#lint
