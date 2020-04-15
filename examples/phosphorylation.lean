import .common

open cpi
open cpi.species

open_locale normalise

def k_react : ℍ := fin_poly.X "k₁"
def k_degrade : ℍ := fin_poly.X "k₂"

def aff : affinity ℍ := affinity.mk_pair k_react

def ω : context := context.extend 1 (context.extend 1 (context.extend 1 context.nil))
def Γ : context := context.extend aff.arity context.nil

@[pattern] def R : reference 1 ω := reference.zero 1
@[pattern] def S : reference 1 ω := reference.extend $ reference.zero 1
@[pattern] def RP : reference 1 ω := reference.extend ∘ reference.extend $ reference.zero 1

def a {Γ} : name (context.extend 2 Γ) := name.zero 0
def b {Γ} : name (context.extend 2 Γ) := name.zero 1

def x {Γ} : name (context.extend 1 Γ) := name.zero 0 /-- An arbitrary name, used in binders. -/

-- R(a) = a.RP(a)
def R_ : choices ℍ ω (context.extend 1 Γ) := x# ⬝' apply RP (name.extend x :: ∅)

-- S(b) = b.S(b)
def S_ : choices ℍ ω (context.extend 1 Γ) := x# ⬝' apply S (name.extend x :: ∅)

-- RP(a) = τ@k₂.R(a)
def RP_ : choices ℍ ω (context.extend 1 Γ) := τ@k_degrade ⬝' apply R (x :: ∅)

def ℓ : lookup ℍ ω Γ := λ n a, begin
  cases a with _ _ _ _ _ a, from R_,
  cases a with _ _ _ _ _ a, from S_,
  cases a with _ _ _ _ _ a, from RP_,
  cases a with _ _ _ _ _ a,
end

def system : process ℂ ℍ ω Γ :=
  fin_poly.X "S" ◯ (apply S (b :: ∅)) |ₚ
  fin_poly.X "R" ◯ (apply R (a :: ∅)) |ₚ
  fin_poly.X "RP" ◯ (apply RP (a :: ∅))

#eval process_immediate aff ℓ conc system

/-
  ((-1•(k₁))•(R•S) + (1•(k₂))•(RP)) • 0([0.0])
  ((-1•(k₂))•(RP) + (1•(k₁))•(R•S)) • 2([0.0])

⇒ dRP/dt = k₁S•R -k₂RP

Note: R = RT - RP, as RT = R + RP
-/
