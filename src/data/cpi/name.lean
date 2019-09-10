namespace cpi

def lvl := ℕ

/-- The set of names within the continuous-π calculus. -/
@[derive decidable_eq]
structure name := mk :: (level : lvl) (idx : ℕ)

/-- A context under which terms may be evaluated.

    Each level of the context holds the arity of the given terms. -/
inductive context
| nil : context
| extend : ℕ → context → context

namespace name
  /-- Is this name valid within the current context? -/
  def well_formed : context → name → Prop
  | context.nil _ := false
  | (context.extend arity _) ⟨ nat.zero, i ⟩ := i < arity
  | (context.extend _ Γ) ⟨ nat.succ l, i ⟩ := well_formed Γ ⟨ l, i ⟩

  /-- Substitute a variable using a level mapping function. -/
  def subst : (lvl → lvl) → name → name
  | ρ ⟨ l, i ⟩ := ⟨ ρ l, i ⟩

  /-- Substitute within an extended scope. -/
  def ext : (lvl → lvl) → lvl → lvl
  | ρ nat.zero := nat.zero
  | ρ (nat.succ l) := nat.succ (ρ l)

  /-- Prove that substituting preserves the well-formed property. -/
  theorem ext.well_formed :
    Π {Γ Δ : context} {ρ : lvl → lvl}
    , (∀ {α : name}, well_formed Γ α → well_formed Δ (subst ρ α))
    → ∀ {n : ℕ} (α : name), well_formed (context.extend n Γ) α → well_formed (context.extend n Δ) (subst (ext ρ) α)
    | Γ Δ ρ imp n ⟨ nat.zero, i ⟩ wf := by { unfold ext well_formed at wf ⊢, assumption }
    | Γ Δ ρ imp n ⟨ nat.succ l, i ⟩ wf := begin
        unfold ext well_formed at wf ⊢,
        have h : well_formed Δ (subst ρ ⟨ l, i ⟩) := imp wf,
        unfold subst at h,
        assumption
      end
end name

end cpi
