import .common

open cpi
open cpi.species

open_locale normalise

def k_bind : ℍ := fin_poly.X "k_bind"
def k_degrade : ℍ := fin_poly.X "k_degrade"
def k_unbind : ℍ := fin_poly.X "k_unbind"
def k_react : ℍ := fin_poly.X "k_react"

def aff : affinity ℍ := affinity.mk_pair k_bind -- x, y

def M : affinity ℍ -- u, r, t
  :=  affinity.mk 3 0 2 k_unbind -- u - t
  ∘[] affinity.mk 3 1 2 k_react -- r - t

def ω : context := context.extend 0 (context.extend M.arity (context.extend 0 (context.extend 0 context.nil)))
def Γ : context := context.extend aff.arity context.nil

def s : name Γ := name.zero ⟨ 0, nat.succ_pos 1 ⟩
def e : name Γ := name.zero ⟨ 1, lt_add_one 1 ⟩

@[pattern] def S : reference 0 ω := reference.zero 0
@[pattern] def E : reference M.arity ω := reference.extend $ reference.zero M.arity
@[pattern] def P₁ : reference 0 ω := reference.extend ∘ reference.extend $ reference.zero 0
@[pattern] def P₂ : reference 0 ω := reference.extend ∘ reference.extend ∘ reference.extend $ reference.zero 0

def x {Γ} : name (context.extend 2 Γ) := name.zero ⟨ 0, nat.succ_pos 1 ⟩
def y {Γ} : name (context.extend 2 Γ) := name.zero ⟨ 1, lt_add_one 1 ⟩

def u {Γ} : name (context.extend M.arity Γ) := name.zero ⟨ 0, nat.succ_pos 2 ⟩
def r {Γ} : name (context.extend M.arity Γ) := name.zero ⟨ 1, int.coe_nat_lt.mp trivial ⟩
def t {Γ} : name (context.extend M.arity Γ) := name.zero ⟨ 2, lt_add_one 2 ⟩

-- S = s(x, y). (x. S + y. (P|P'))
def Sₛ_ : species ℍ ω Γ :=
  s #( 2 ) ⬝ Σ# ( whole.cons (x #) (apply S ∅)
                $ whole.cons (y #) (apply P₁ ∅ |ₛ apply P₂ ∅)
                $ whole.empty )

def S_ : choices ℍ ω Γ :=
  s #( 2 ) ⬝' Σ# ( whole.cons (x #) (apply S ∅)
                 ∘ whole.cons (y #) (apply P₁ ∅ |ₛ apply P₂ ∅)
                 $ whole.empty )

-- E = ν(u, r, t : M) . e⟨u, r⟩. t. E)
def Eₛ : reference 0 ω := reference.zero 0
def Eₛ_ : species ℍ ω Γ :=
  ν(M) (name.extend e #⟨ [u, r] ⟩) ⬝ (name.extend t # ⬝ apply Eₛ ∅)

def E_ : choices ℍ ω (context.extend M.arity Γ) :=
  (name.extend e #⟨ [u, r] ⟩) ⬝' (name.extend t # ⬝ ν(M) apply E (u :: r :: t :: ∅))

-- P = P' = τ@k_degrade. 0
def Pₛ_ : species ℍ ω Γ := τ@k_degrade ⬝ nil

def P_ : choices ℍ ω Γ := τ@k_degrade ⬝' nil
def P'_ : species ℍ ω Γ := Σ# P_

def ℓ : lookup ℍ ω Γ
| _ S := species.rename name.extend S_
| _ E := E_
| _ P₁ := species.rename name.extend P_
| _ P₂ := species.rename name.extend P_
| (nat.succ n) (reference.extend (reference.extend a)) := by { cases a, cases a_a, cases a_a_a }

-- S [s]—→ (; x, y) (x.S + y.(P|P'))
example : (Σ# S_) [ℓ, # s]⟶ (production.concretion (#( vector.nil; 2 )
  Σ# ( whole.cons (x#) (apply S ∅)
     ∘ whole.cons (y#) (apply P₁ ∅ |ₛ apply P₂ ∅)
     $ whole.empty )))
:= transition.choice₁ _ _ _ _ _ _

-- P₁ [τ@k_degrade]⟶ 0
example : P'_ [ℓ, τ@' k_degrade]⟶ (production.species nil)
  := transition.choice₂ k_degrade whole.nil whole.empty

/- Various intermediates -/
def E'_ {Γ} : species ℍ ω Γ := ν(M) apply E (u :: r :: t :: ∅)
def C'_ : species ℍ ω Γ :=
  ν(M) ( ( Σ# ( whole.cons (u#) (apply S ∅)
              $ whole.cons (r#) (apply P₁ ∅ |ₛ apply P₂ ∅)
              $ whole.empty ) )
       |ₛ t# ⬝ E'_)

#eval process_immediate aff ℓ conc ((2 : ℂ) ◯ E'_ |ₚ 2 ◯ (apply S ∅) )

def system : process ℂ ℍ ω Γ :=
  fin_poly.X "S" ◯ (apply S ∅) |ₚ
  fin_poly.X "E" ◯ E'_ |ₚ
  fin_poly.X "S" ◯ C'_ |ₚ
  fin_poly.X "P₁" ◯ (apply P₁ ∅) |ₚ
  fin_poly.X "P₂" ◯ (apply P₂ ∅)

#eval process_immediate aff ℓ conc system

/-
-- Run the result of the above through enzyme.py

(-1•(E•S•k_bind) + 1•(S•k_react) + 1•(S•k_unbind)) • E
(-1•(E•S•k_bind) + 1•(S•k_unbind)) • S
(-1•(P₁•k_degrade) + 1•(S•k_react)) • P₁
(-1•(P₂•k_degrade) + 1•(S•k_react)) • P₂
(-1•(S•k_react) + -1•(S•k_unbind) + 1•(E•S•k_bind)) • C
-/
