import .common

open cpi
open cpi.species

open_locale normalise

def k_react : ℍ := fin_poly.X "k₁"
def k_degrade : ℍ := fin_poly.X "k₂"

def aff : affinity ℍ := affinity.mk_pair k_react

def ω : context := context.extend 0 (context.extend 0 (context.extend 0 context.nil))
def Γ : context := context.extend aff.arity context.nil

@[pattern] def R : reference 0 ω := reference.zero 0
@[pattern] def S : reference 0 ω := reference.extend $ reference.zero 0
@[pattern] def RP : reference 0 ω := reference.extend ∘ reference.extend $ reference.zero 0

def a {Γ} : name (context.extend 2 Γ) := name.zero 0
def b {Γ} : name (context.extend 2 Γ) := name.zero 1

-- R = a.RP
def R_ : choices ℍ ω Γ := a# ⬝' apply RP ∅

-- S = b.S
def S_ : choices ℍ ω Γ := b# ⬝' apply S ∅

-- RP = τ@k₂.R
def RP_ : choices ℍ ω Γ := τ@k_degrade ⬝' apply R ∅

def ℓ : lookup ℍ ω Γ := λ n a, begin
  cases a with _ _ _ _ _ a, from species.rename name.extend R_,
  cases a with _ _ _ _ _ a, from species.rename name.extend S_,
  cases a with _ _ _ _ _ a, from species.rename name.extend RP_,
  cases a with _ _ _ _ _ a,
end

def system : process ℂ ℍ ω Γ :=
  fin_poly.X "S" ◯ (apply S ∅) |ₚ
  fin_poly.X "R" ◯ (apply R ∅) |ₚ
  fin_poly.X "RP" ◯ (apply RP ∅)

#eval process_immediate aff ℓ conc system

/-
  ((-1•(k₁))•(R•S) + (1•(k₂))•(RP)) • 0([0.0])
  ((-1•(k₂))•(RP) + (1•(k₁))•(R•S)) • 2([0.0])

⇒ dRP/dt = k₁S•R -k₂RP

Note: R = RT - RP, as RT = R + RP
-/
