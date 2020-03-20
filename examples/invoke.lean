import data.cpi.semantics.basic
-- import data.cpi.semantics.with_exact
import data.cpi.semantics.with_normalise

open cpi
open cpi.species

open_locale normalise

def aff : affinity ℚ :=
  { arity := 2,
    f := λ x y,
      if h : (x = 0 ∧ y = 1) ∨ (y = 0 ∧ x = 1) then
        some (1/2)
      else
        none,
    symm := λ x y, begin
      by_cases x = 0 ∧ y = 1 ∨ y = 0 ∧ x = 1,
      simp only [dif_pos h, dif_pos (or.swap h)],
      simp only [dif_neg h, dif_neg (h ∘ or.swap)],
    end }


def ω : context := context.extend 0  $ context.extend 0 context.nil
def A : reference 0 ω := reference.extend (reference.zero 0)
def B : reference 0 ω := reference.zero 0

def Γ : context := context.extend aff.arity context.nil

def a : name Γ := name.zero ⟨ 0, nat.succ_pos 1 ⟩
def b : name Γ := name.zero ⟨ 1, lt_add_one 1 ⟩

local notation a ` ⬝' ` b := whole.cons a b whole.empty

def ℓ : lookup ℚ ω Γ
| ._ (reference.zero n) := species.rename name.extend (a # ⬝' (apply A vector.nil |ₛ apply A vector.nil))
| ._ (reference.extend n) := species.rename name.extend (b # ⬝' nil)

def C : choices ℚ ω Γ := (τ@(1/6) ⬝' apply B vector.nil)
def conc := function.embedding.refl ℚ

def immediate_ABC : process_space ℚ ℚ ω Γ := process_immediate aff ℓ conc
  (1 ◯ (apply A vector.nil) |ₚ 1 ◯ (apply B vector.nil) |ₚ 1 ◯ (Σ# C))

#eval immediate_ABC
