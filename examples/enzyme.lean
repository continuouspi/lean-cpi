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
def Sₛ_ : species ℝ ω Γ :=
  s #( 2 ) ⬝ Σ# ( whole.cons (x #) (apply S ∅)
                $ whole.cons (y #) (apply P₁ ∅ |ₛ apply P₂ ∅)
                $ whole.empty )

def S_ : choices ℝ ω Γ :=
  s #( 2 ) ⬝' Σ# ( whole.cons (x #) (apply S ∅)
                 ∘ whole.cons (y #) (apply P₁ ∅ |ₛ apply P₂ ∅)
                 $ whole.empty )

-- E = ν(u, r, t : M) . e⟨u, r⟩. t. E)
def Eₛ_ : species ℝ ω Γ :=
  ν(M) (name.extend e #⟨ [u, r] ⟩) ⬝ (name.extend t # ⬝ apply Eₛ ∅)

def E_ : choices ℝ ω (context.extend M.arity Γ) :=
  (name.extend e #⟨ [u, r] ⟩) ⬝' (name.extend t # ⬝ ν(M) apply E (u :: r :: t :: ∅))

def S'_ : species ℝ ω Γ := Σ# S_
def E'_ : species ℝ ω Γ := ν(M) apply E (u :: r :: t :: ∅)

-- P = P' = τ@k_degrade. 0
def Pₛ_ : species ℝ ω Γ := τ@k_degrade ⬝ nil

def P_ : choices ℝ ω Γ := τ@k_degrade ⬝' nil
def P'_ : species ℝ ω Γ := Σ# P_

def ℓ : lookup ℝ ω Γ
| _ S := species.rename name.extend S_
| _ E := E_
| _ P₁ := species.rename name.extend P_
| _ P₂ := species.rename name.extend P_
| (nat.succ n) (reference.extend (reference.extend a)) := by { cases a, cases a_a, cases a_a_a }

-- S [s]—→ (; x, y) (x.S + y.(P|P'))
example : S'_ [ℓ, # s]⟶ (production.concretion (#( vector.nil; 2 )
  Σ# ( whole.cons (x#) (apply S ∅)
     ∘ whole.cons (y#) (apply P₁ ∅ |ₛ apply P₂ ∅)
     $ whole.empty )))
:= transition.choice₁ _ _ _ _ _

-- P₁ [τ@k_degrade]⟶ 0
example : P'_ [ℓ, τ@' k_degrade]⟶ (production.species nil)
  := transition.choice₂ k_degrade whole.nil whole.empty

-- set_option pp.notation false
example : E'_ [ℓ, #e]⟶ (production.concretion
  (ν'(M)
    #(vector.map (name.mk_apply (u :: r :: t :: ∅)) (u :: r :: vector.nil) ; 0)
    rename (name.ext (name.mk_apply (u :: r :: t :: ∅)))
    (rename (name.ext (name.ext name.extend))
      (name.extend t#(0) ⬝ ν(M) whole.apply E (u :: r :: t :: ∅)))))
:= begin

  have :
    (Σ# (rename (name.ext (@name.extend _ M.arity)) E_))
      [ (lookup.rename name.extend ∘ lookup.rename name.extend $ ℓ)
      , # (name.extend (name.extend e))
      ]⟶
      (production.concretion
        (#((u :: r :: vector.nil) ; 0) (rename (name.ext (name.ext name.extend))
          (name.extend t# ⬝ ν(M) whole.apply E (u :: r :: t :: ∅))))),
  {
    simp [E_, u, r],
    from transition.choice₁
      (name.extend (name.extend e))
      (u :: r :: list.nil)
      0 (rename (name.ext (name.ext name.extend))
          (name.extend t# ⬝ ν(M) whole.apply E (u :: r :: t :: ∅))) whole.empty,
  },

  have : E'_ [ℓ, _]⟶ _,
  {
    refine transition.ν₁ M _,

    show (whole.apply E (u :: r :: t :: ∅))
      [lookup.rename name.extend ℓ, label.rename name.extend (# e)]⟶ _,
    have h := transition.defn (lookup.rename name.extend ℓ) E (u :: r :: t :: ∅) _,

    show (Σ# lookup.rename name.extend ℓ (M.arity) E)
      [lookup.rename name.extend (lookup.rename name.extend ℓ), _]⟶ _,
    from this,

    simp [name.mk_apply, label.rename, production.rename, concretion.rename] at h,
    from h,
  },
  from this,
end
end
