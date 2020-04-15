import .common

open cpi
open cpi.species

open_locale normalise

def k1 : ℍ := fin_poly.X "k₁"
def k2 : ℍ := fin_poly.X "k₂"
def k3 : ℍ := fin_poly.X "k₃"
def k4 : ℍ := fin_poly.X "k₄"

def aff : affinity ℍ := affinity.mk_pair k2

def ω : context := context.extend 0 (context.extend 0 (context.extend 0 context.nil))
def Γ : context := context.extend aff.arity context.nil

@[pattern] def R : reference 0 ω := reference.zero 0
@[pattern] def S : reference 0 ω := reference.extend $ reference.zero 0
@[pattern] def X : reference 0 ω := reference.extend ∘ reference.extend $ reference.zero 0

def a {Γ} : name (context.extend 2 Γ) := name.zero 0
def b {Γ} : name (context.extend 2 Γ) := name.zero 1

-- R = a.0
def R_ : choices ℍ ω Γ := a# ⬝' nil

-- S = τ@2.(S|R) + τ@1.(S|X)
def S_ : choices ℍ ω Γ
  := whole.cons τ@k1 (apply S ∅ |ₛ apply R ∅)
   ∘ whole.cons τ@k3 (apply S ∅ |ₛ apply X ∅)
   $ whole.empty

-- X = τ@1.0 + b.X
def X_ : choices ℍ ω Γ
  := whole.cons τ@k4 nil
   ∘ whole.cons (b#) (apply X ∅)
   $ whole.empty

def ℓ : lookup ℍ ω Γ := λ n a, begin
  cases a with _ _ _ _ _ a, from species.rename name.extend R_,
  cases a with _ _ _ _ _ a, from species.rename name.extend S_,
  cases a with _ _ _ _ _ a, from species.rename name.extend X_,
  cases a with _ _ _ _ _ a,
end

def system : process ℍ ℍ ω Γ :=
  fin_poly.X "S" ◯ (apply S ∅) |ₚ
  fin_poly.X "R" ◯ (apply R ∅) |ₚ
  fin_poly.X "X" ◯ (apply X ∅)

#eval process_immediate aff ℓ (function.embedding.refl _) system

/-
(-1•(R•X•k₂) + 1•(S•k₁)) • 0([])
(-1•(X•k₄) + 1•(S•k₃)) • 2([])

⇒ dR/dt = k₁S - k₂X•R
⇒ dX/dt = k₃S - k₄X
-/
