import data.cpi.species

namespace cpi

/-- A concretion represents the potential for a species to interact with another.
    -/
@[derive decidable_eq, nolint has_inhabited_instance]
inductive concretion (ℍ : Type) (ω : context) : context → ℕ → ℕ → Type
| apply {Γ} {b} (bs : vector (name Γ) b) (y : ℕ)
  : species ℍ ω (context.extend y Γ)
  → concretion Γ b y
| parallel₁ {Γ} {b y} : concretion Γ b y → species ℍ ω Γ → concretion Γ b y
| parallel₂ {Γ} {b y} : species ℍ ω Γ → concretion Γ b y → concretion Γ b y
| restriction {Γ} {b y} (M : affinity ℍ)
  : concretion (context.extend M.arity Γ) b y
  → concretion Γ b y

notation `#(` b ` ; ` y `)` A := concretion.apply b y A

reserve infixr ` |₁ ` :50
reserve infixr ` |₂ ` :50

infixr ` |₁ ` := concretion.parallel₁
infixr ` |₂ ` := concretion.parallel₂

notation `ν'(` M `) ` A := concretion.restriction M A

variables {ℍ : Type} {ω : context}

namespace concretion

section free
  /-- Determine whether a level occurs within a concretion. -/
  def free_in : ∀ {Γ} {b y} (l : level Γ) (F : concretion ℍ ω Γ b y), Prop
  | Γ b y l (#(bs; _) A) := (∃ b ∈ bs.val, l ∈ b) ∨ level.extend l ∈ A
  | Γ b y l (F |₁ A) := free_in l F ∨ l ∈ A
  | Γ b y l (A |₂ F) := l ∈ A ∨ free_in l F
  | Γ b y l (ν'(M) F) := free_in (level.extend l) F

  instance {Γ} {b y} : has_mem (level Γ) (concretion ℍ ω Γ b y) := ⟨ free_in ⟩

  private def free_in_decide : ∀ {Γ} {b y} (l : level Γ) (F : concretion ℍ ω Γ b y), decidable (free_in l F)
  | Γ b y l (#(bs; _) A) := by { unfold free_in, apply_instance }
  | Γ b y l (F |₁ A) := @or.decidable _ _ (free_in_decide l F) _
  | Γ b y l (A |₂ F) := @or.decidable _ _ _ (free_in_decide l F)
  | Γ b y l (ν'(M) F) := free_in_decide (level.extend l) F

  instance free_in.decidable {Γ} {b y} {l} {F : concretion ℍ ω Γ b y} : decidable (l ∈ F)
    := free_in_decide l F
end free

section rename
  /-- Rename a concretion. -/
  def rename : ∀ {Γ Δ} {b y} (ρ : name Γ → name Δ), concretion ℍ ω Γ b y → concretion ℍ ω Δ b y
  | Γ Δ b y ρ (#(bs; _) A) := #( vector.map ρ bs; y) species.rename (name.ext ρ) A
  | Γ Δ b y ρ (F |₁ A) := rename ρ F |₁ species.rename ρ A
  | Γ Δ b y ρ (A |₂ F) := species.rename ρ A |₂ rename ρ F
  | Γ Δ b y ρ (ν'(M) A) := ν'(M) (rename (name.ext ρ) A)

  lemma rename_id
    : ∀ {Γ} {b y} (F : concretion ℍ ω Γ b y)
    , rename id F = F
  | Γ b ._ (#(⟨ list, n ⟩; y) A) := begin
      simp only [rename, vector.map, list.map_id, subtype.mk_eq_mk],
      rw name.ext_id,
      from ⟨ rfl, species.rename_id A ⟩
    end
  | Γ b y (F |₁ A) := begin
      simp only [rename],
      from ⟨ rename_id F, species.rename_id A ⟩
    end
  | Γ b y (A |₂ F) := begin
      simp only [rename],
      from ⟨ species.rename_id A, rename_id F ⟩
    end
  | Γ b y (ν'(M) F) := begin
      simp only [rename], rw name.ext_id,
      from ⟨ rfl, heq_of_eq (rename_id F) ⟩,
    end

  lemma rename_compose :
    ∀ {Γ Δ η} {b y} (ρ : name Γ → name Δ) (σ : name Δ → name η) (A : concretion ℍ ω Γ b y)
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

end rename

end concretion

/-- A quotient of all equivalent concretions. -/
@[nolint has_inhabited_instance]
def concretion' (ℍ : Type) (ω Γ : context) (b y : ℕ) [r : setoid (concretion ℍ ω Γ b y)]
  := quotient r

end cpi

#lint-
