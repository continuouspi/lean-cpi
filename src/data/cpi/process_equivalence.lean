import data.cpi.basic
import data.cpi.species_equivalence
import data.rule_equiv

namespace cpi

namespace process
  inductive rewrite {Γ : context} : process Γ → process Γ → Type
  -- Projection
  | ξ_species   : ∀ {c : ℝ≥0} {A B : species Γ}, A ≈ B → rewrite (c • A) (c • B)
  | ξ_parallel₁ : ∀ {P P' Q : process Γ}, rewrite P P' → rewrite (P |ₚ Q) (P' |ₚ Q)
  | ξ_parallel₂ : ∀ {P Q Q' : process Γ}, rewrite Q Q' → rewrite (P |ₚ Q) (P |ₚ Q')

  -- Monoidic properties
  | parallel_nil   : ∀ {P : process Γ} {c : ℝ≥0}, rewrite (P |ₚ c • species.nil) P
  | parallel_sym   : ∀ {P Q : process Γ}, rewrite (P |ₚ Q) (Q |ₚ P)
  | parallel_assoc : ∀ {P Q R : process Γ}, rewrite ((P |ₚ Q) |ₚ R) (P |ₚ (Q |ₚ R))

  -- Join identical species together.
  | join  : ∀ {A : species Γ} {c d : ℝ≥0}, rewrite (c • A |ₚ d • A) ((c + d) • A)

  -- local infix ` ⟶ `:51 := rewrite
  -- def subst : ∀ {Γ Δ} {A B : process Γ} (ρ : name Γ → name Δ)
  --             , A ⟶ B → process.subst ρ A ⟶ process.subst ρ B

  def equiv {Γ} : process Γ → process Γ → Prop := rule_equiv rewrite

  instance {Γ} : is_equiv (process Γ) equiv := rule_equiv.is_equiv rewrite
  instance {Γ} : setoid (process Γ) := rule_equiv.setoid rewrite
  instance setoid.is_equiv {Γ} : is_equiv (process Γ) has_equiv.equiv :=
    rule_equiv.is_equiv rewrite
end process

end cpi
