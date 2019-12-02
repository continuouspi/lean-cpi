import data.cpi.transition data.real.basic

open cpi
open cpi.species

section

parameters (k_bind k_degrade : ℝ)

def aff : affinity ℝ :=
  { arity := 2,
    f := λ x y,
      if h : (x = 0 ∧ y = 1) ∨ (y = 0 ∧ x = 1) then
        some k_bind
      else
        none,
    symm := λ x y, begin
      by_cases x = 0 ∧ y = 1 ∨ y = 0 ∧ x = 1,
      simp only [dif_pos h, dif_pos (or.swap h)],
      simp only [dif_neg h, dif_neg (h ∘ or.swap)],
    end }

def M : affinity ℝ :=
  { arity := 3,
    f := sorry,
    symm := sorry }

def ω : context := context.extend 0 (context.extend M.arity (context.extend 0 (context.extend 0 context.nil)))
def Γ : context := context.extend aff.arity context.nil

def s : name Γ := name.zero ⟨ 0, nat.succ_pos 1 ⟩
def e : name Γ := name.zero ⟨ 1, lt_add_one 1 ⟩

@[pattern] def S : reference 0 ω := reference.zero 0
@[pattern] def E : reference M.arity ω := reference.extend $ reference.zero M.arity
@[pattern] def P : reference 0 ω := reference.extend ∘ reference.extend $ reference.zero 0
@[pattern] def P' : reference 0 ω := reference.extend ∘ reference.extend ∘ reference.extend $ reference.zero 0

def x {Γ} : name (context.extend 2 Γ) := name.zero ⟨ 0, nat.succ_pos 1 ⟩
def y {Γ} : name (context.extend 2 Γ) := name.zero ⟨ 1, lt_add_one 1 ⟩

def u {Γ} : name (context.extend M.arity Γ) := name.zero ⟨ 0, nat.succ_pos 2 ⟩
def r {Γ} : name (context.extend M.arity Γ) := name.zero ⟨ 1, int.coe_nat_lt.mp trivial ⟩
def t {Γ} : name (context.extend M.arity Γ) := name.zero ⟨ 2, lt_add_one 2 ⟩

local notation a ` ⬝' ` b := whole.cons a b whole.empty

-- S = s(x, y). (x. S + y. (P|P'))
def S_ : choices ℝ ω Γ :=
  s #( 2 ) ⬝' Σ# ( whole.cons (x #) (apply S vector.nil)
                ∘ whole.cons (y #) (apply P vector.nil |ₛ apply P' vector.nil)
                $ whole.empty )

-- E = ν(u, r, t : M) . e⟨u, r⟩. t. E)
-- def E_ : species ℝ ω Γ :=
--   ν(M) (name.extend e #⟨ [u, r] ⟩) ⬝ (name.extend t # ⬝ apply E vector.nil)
def E_ : choices ℝ ω (context.extend M.arity Γ) :=
  (name.extend e #⟨ [u, r] ⟩) ⬝' (name.extend t # ⬝ ν(M) apply E (u :: r :: t :: vector.nil))

-- P = P' = τ@k_degrade. 0
def P_ : choices ℝ ω Γ := τ@k_degrade ⬝' nil

def ℓ : lookup ℝ ω Γ
| _ S := species.rename name.extend S_
| _ E := E_
| _ P := species.rename name.extend P_
| _ P' := species.rename name.extend P_
| (nat.succ n) (reference.extend (reference.extend a)) := by { cases a, cases a_a, cases a_a_a }

-- S [s]—→ (; x, y) (x.S + y.(P|P'))
example : (Σ# S_) [ℓ, # s]⟶ (production.concretion (#( vector.nil; 2 )
  Σ# ( whole.cons (x#) (apply S vector.nil)
     ∘ whole.cons (y#) (apply P vector.nil |ₛ apply P' vector.nil)
     $ whole.empty )))
:= transition.choice₁ _ _ _ _ _

end
