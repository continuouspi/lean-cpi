import data.cpi.species

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi

inductive concretion : context → ℕ → ℕ → Type
| apply : ∀ {Γ} {b} (bs : vector (name Γ) b) (y : ℕ)
        , species (context.extend y Γ)
        → concretion Γ b y
| parallel₁ : ∀ {Γ} {b y}, concretion Γ b y → species Γ → concretion Γ b y
| parallel₂ : ∀ {Γ} {b y}, species Γ → concretion Γ b y → concretion Γ b y
| restriction : ∀ {Γ} {b y} (M : affinity)
              , concretion (context.extend M.arity Γ) b y
              → concretion Γ b y

notation `#(` b ` ; ` y `)` A := concretion.apply b y A

reserve infixr ` |₁ ` :50
reserve infixr ` |₂ ` :50

infixr ` |₁ ` := concretion.parallel₁
infixr ` |₂ ` := concretion.parallel₂

notation `ν'(` M `) ` A := concretion.restriction M A


namespace concretion
  def rename :
    ∀ {Γ Δ} {b y} (ρ : name Γ → name Δ)
    , concretion Γ b y → concretion Δ b y
  | Γ Δ b y ρ (#(bs; _) A) := #( vector.map ρ bs; y) species.rename (name.ext ρ) A
  | Γ Δ b y ρ (F |₁ A) := rename ρ F |₁ species.rename ρ A
  | Γ Δ b y ρ (A |₂ F) := species.rename ρ A |₂ rename ρ F
  | Γ Δ b y ρ (ν'(M) A) := ν'(M) (rename (name.ext ρ) A)

  theorem rename_compose :
    ∀ {Γ Δ η} {b y} (ρ : name Γ → name Δ) (σ : name Δ → name η) (A : concretion Γ b y)
    , rename σ (rename ρ A) = rename (σ ∘ ρ) A
  | Γ Δ η b ._ ρ σ (#(⟨ elem, n ⟩; y) A) := begin
      unfold rename vector.map,
      rw [species.rename_compose _ _ A, name.ext_comp],
      simp
    end
  | Γ Δ η b y ρ σ (F |₁ A) := begin
      unfold rename,
      rw [rename_compose ρ σ F, species.rename_compose ρ σ A]
    end
  | Γ Δ η b y ρ σ (A |₂ F) := begin
      unfold rename,
      rw [rename_compose ρ σ F, species.rename_compose ρ σ A]
    end
  | Γ Δ η b y ρ σ (ν'(M) A) := begin
      unfold rename,
      rw [rename_compose (name.ext ρ) (name.ext σ) A, name.ext_comp]
    end
end concretion

end cpi

#sanity_check
