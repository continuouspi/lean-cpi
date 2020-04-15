import .common

open cpi
open cpi.species

open_locale normalise

def k_ambient : ℍ := fin_poly.X "k₀"
def k_react : ℍ := fin_poly.X "k₁"
def k_degrade : ℍ := fin_poly.X "k₂"

def aff : affinity ℍ := ∅

def ω : context := context.extend 0 (context.extend 0 (context.extend 0 context.nil))
def Γ : context := context.extend aff.arity context.nil

@[pattern] def A : reference 0 ω := reference.zero 0
@[pattern] def S : reference 0 ω := reference.extend $ reference.zero 0
@[pattern] def R : reference 0 ω := reference.extend ∘ reference.extend $ reference.zero 0

-- A = τ@k₀(A|R)
def A_ : choices ℍ ω Γ := τ@k_ambient ⬝' (apply A ∅ |ₛ apply R ∅)

-- S = τ@k₁.(S|R)
def S_ : choices ℍ ω Γ := τ@k_react ⬝' (apply S ∅ |ₛ apply R ∅)

-- R = τ@k₂. 0
def R_ : choices ℍ ω Γ := τ@k_degrade ⬝' nil

def ℓ : lookup ℍ ω Γ
| _ A := species.rename name.extend A_
| _ S := species.rename name.extend S_
| _ R := species.rename name.extend R_
| (nat.succ n) (reference.extend (reference.extend a)) := by { cases a, cases a_a }

def system : process ℂ ℍ ω Γ :=
  1 ◯ (apply A ∅) |ₚ
  fin_poly.X "S" ◯ (apply S ∅) |ₚ
  fin_poly.X "R" ◯ (apply R ∅)

#eval process_immediate aff ℓ conc system

/-
  (-1•(R•k₂) + 1•(S•k₁) + 1•(k₀)) • 2([])
⇒ dR/dt = k₀ + k₁S -k₂R
-/
