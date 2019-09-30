import data.cpi.species

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi

variable {ω : environment}

/-- The set of processes. Defined as one or more species, each with a
    non-negative concentration.

    The context parameter represents the "global affinity network", in which
    all processes are evaluated. -/
inductive process : context ω → Type
| one      {Γ} : ℝ≥0 → species Γ → process Γ
| parallel {Γ} : process Γ → process Γ → process Γ

infix ` • `:60 := process.one
infixr ` |ₚ `:50 := process.parallel

end cpi

#sanity_check
