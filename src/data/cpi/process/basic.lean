import data.cpi.species

namespace cpi

/-- The set of processes. Defined as one or more species, each with a
    non-negative concentration. Processes range over the type of concentrations
    (ℂ) and affinities/reaction rates (ℍ).

    The context parameter represents the "global affinity network", in which
    all processes are evaluated. -/
inductive process (ℂ ℍ : Type) (ω : context) : context → Type
| one      {Γ} : ℂ → species ℍ ω Γ → process Γ
| parallel {Γ} : process Γ → process Γ → process Γ

infix ` ◯ `:60 := process.one
infixr ` |ₚ `:50 := process.parallel

end cpi

#lint-
