import data.cpi.semantics.basic
import data.cpi.semantics.with_normalise

open cpi
open cpi.species

open_locale normalise

def aff : affinity ℚ :=
  { arity := 2,
    f := λ x y,
      if h : (x = 0 ∧ y = 1) ∨ (y = 0 ∧ x = 1) then
        some (1/3)
      else
        none,
    symm := λ x y, begin
      by_cases x = 0 ∧ y = 1 ∨ y = 0 ∧ x = 1,
      simp only [dif_pos h, dif_pos (or.swap h)],
      simp only [dif_neg h, dif_neg (h ∘ or.swap)],
    end }


def ω : context := context.nil
def Γ : context := context.extend aff.arity context.nil
def ℓ : lookup ℚ ω Γ
| n r := by cases r

def a : name Γ := name.zero ⟨ 0, nat.succ_pos 1 ⟩
def b : name Γ := name.zero ⟨ 1, lt_add_one 1 ⟩

@[pattern] def A : species ℚ ω Γ := a # ⬝ nil
@[pattern] def B : species ℚ ω Γ := b # ⬝ nil
@[pattern] def AB : species ℚ ω Γ := A |ₛ B

def conc := function.embedding.refl ℚ

/-- ∂(c•(A|B)) -/
def potential_species : interaction_space ℚ ℚ ω Γ := process_potential aff ℓ (1 ◯ AB)

/-- d(c•(A|B))/dt -/
def immediate_species : process_space ℚ ℚ ω Γ := process_immediate aff ℓ conc (1 ◯ AB)

#eval immediate_species

/- -------------------------------------------- -/

/-- ∂(c•A) -/
def potential_A : interaction_space ℚ ℚ ω Γ := process_potential aff ℓ (1 ◯ A)

/-- ∂(c•B) -/
def potential_B : interaction_space ℚ ℚ ω Γ := process_potential aff ℓ (1 ◯ A)

/-- ∂(c•A || c•B) -/
def potential_proc : interaction_space ℚ ℚ ω Γ := process_potential aff ℓ (1 ◯ A |ₚ 1 ◯ B)

/-- d(c•A)/dt -/
def immediate_A : process_space ℚ ℚ ω Γ := process_immediate aff ℓ conc (1 ◯ A)

/-- d(c•A)/dt -/
def immediate_B : process_space ℚ ℚ ω Γ := process_immediate aff ℓ conc (1 ◯ B)

/-- d(c•A || c•B)/dt -/
def immediate_proc : process_space ℚ ℚ ω Γ := process_immediate aff ℓ conc (1 ◯ A |ₚ 1 ◯ B)

#eval potential_B
