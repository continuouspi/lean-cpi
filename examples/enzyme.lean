import data.cpi.semantics.with_normalise data.cpi.semantics.ode

open cpi
open cpi.species

open_locale normalise

def ℍ : Type := fin_poly string ℚ
instance : half_ring ℍ := fin_poly.half_ring string ℚ
instance : has_repr ℍ := fin_poly.has_repr string ℚ

def k_bind : ℍ := fin_poly.X "k_bind"
def k_degrade : ℍ := fin_poly.X "k_degrade"
def k_unbind : ℍ := fin_poly.X "k_unbind"
def k_react : ℍ := fin_poly.X "k_react"

def aff : affinity ℍ :=
  { arity := 2, -- x, y
    f := λ x y,
      if (x = 0 ∧ y = 1) ∨ (y = 0 ∧ x = 1) then some k_bind
      else none,
    symm := λ x y, begin
      by_cases x = 0 ∧ y = 1 ∨ y = 0 ∧ x = 1,
      simp only [if_pos h, if_pos (or.swap h)],
      simp only [if_neg h, if_neg (h ∘ or.swap)],
    end }

def M : affinity ℍ :=
  { arity := 3, -- u, r, t
    f := λ x y,
      if (x = 0 ∧ y = 2) ∨ (y = 0 ∧ x = 2) then some k_unbind -- u - t
      else if (x = 1 ∧ y = 2) ∨ (y = 1 ∧ x = 2) then some k_react -- r - t
      else none,
    symm := λ x y, begin
      by_cases (x = 0 ∧ y = 2) ∨ (y = 0 ∧ x = 2),
      simp only [if_pos h, if_pos (or.swap h)],
      simp only [if_neg h, if_neg (h ∘ or.swap)],
      clear h,

      by_cases  (x = 1 ∧ y = 2) ∨ (y = 1 ∧ x = 2),
      simp only [if_pos h, if_pos (or.swap h)],
      simp only [if_neg h, if_neg (h ∘ or.swap)],
    end }

def ω : context := context.extend 0 (context.extend M.arity (context.extend 0 (context.extend 0 context.nil)))
def Γ : context := context.extend aff.arity context.nil

def s : name Γ := name.zero ⟨ 0, nat.succ_pos 1 ⟩
def e : name Γ := name.zero ⟨ 1, lt_add_one 1 ⟩

@[pattern] def S : reference 0 ω := reference.zero 0
@[pattern] def E : reference M.arity ω := reference.extend $ reference.zero M.arity
@[pattern] def Eₛ : reference 0 ω := reference.zero 0
@[pattern] def P₁ : reference 0 ω := reference.extend ∘ reference.extend $ reference.zero 0
@[pattern] def P₂ : reference 0 ω := reference.extend ∘ reference.extend ∘ reference.extend $ reference.zero 0

def x {Γ} : name (context.extend 2 Γ) := name.zero ⟨ 0, nat.succ_pos 1 ⟩
def y {Γ} : name (context.extend 2 Γ) := name.zero ⟨ 1, lt_add_one 1 ⟩

def u {Γ} : name (context.extend M.arity Γ) := name.zero ⟨ 0, nat.succ_pos 2 ⟩
def r {Γ} : name (context.extend M.arity Γ) := name.zero ⟨ 1, int.coe_nat_lt.mp trivial ⟩
def t {Γ} : name (context.extend M.arity Γ) := name.zero ⟨ 2, lt_add_one 2 ⟩

local notation a ` ⬝' ` b := whole.cons a b whole.empty

instance vector.has_empty {α : Type} : has_emptyc (vector α 0) := { emptyc := vector.nil }

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

def ℂ : Type := fin_poly (species ℍ ω Γ) ℍ
instance : half_ring ℂ := fin_poly.half_ring _ _
instance : has_repr ℂ := fin_poly.has_repr _ _

def conc : ℍ ↪ ℂ := fin_poly.C.embed

#eval process_immediate aff ℓ conc ((2 : ℂ) ◯ E'_ |ₚ 2 ◯ (apply S ∅) )

def system : process ℂ ℍ ω Γ :=
  (fin_poly.X (apply S ∅)) ◯ (apply S ∅) |ₚ
  (fin_poly.X E'_) ◯ E'_ |ₚ
  (fin_poly.X C'_) ◯ C'_ |ₚ
  (fin_poly.X (apply P₁ ∅)) ◯ (apply P₁ ∅) |ₚ
  (fin_poly.X (apply P₂ ∅)) ◯ (apply P₂ ∅)

#eval process_immediate aff ℓ conc system

/-
-- Run the result of the above through enzyme.py

((-1•("k_bind"))•(E•S) + (1•("k_react") + 1•("k_unbind"))•(C)) • E
((-1•("k_bind"))•(E•S) + (1•("k_unbind"))•(C)) • S
((-1•("k_degrade"))•(P₁) + (1•("k_react"))•(C)) • P₁
((-1•("k_degrade"))•(P₂) + (1•("k_react"))•(C)) • P₂
((-1•("k_react") + -1•("k_unbind"))•(C) + (1•("k_bind"))•(E•S)) • C
-/
