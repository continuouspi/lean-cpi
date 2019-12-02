import data.cpi.semantics.space

namespace cpi

variables {ℍ : Type} {ω : context} [half_ring ℍ] [decidable_eq ℍ]
local attribute [instance] prime_equal concretion_equal

/-- The main body of the interaction tensor. Split out into a separate function
    to make unfolding possible. -/
private noncomputable def interaction_tensor_worker (M: affinity ℍ)
  : ( quotient (@species.setoid ℍ ω (context.extend M.arity context.nil))
    × (Σ' (b y), quotient (@concretion.setoid ℍ ω (context.extend M.arity context.nil) b y))
    × name (context.extend M.arity context.nil))
  → ( quotient (@species.setoid ℍ ω (context.extend M.arity context.nil))
    × (Σ' (b y), quotient (@concretion.setoid ℍ ω (context.extend M.arity context.nil) b y))
    × name (context.extend M.arity context.nil))
  → process_space ℍ ω (context.extend M.arity context.nil)
| ⟨ A, ⟨ bF, yF, F ⟩, a ⟩ ⟨ B, ⟨ bG, yG, G ⟩, b ⟩ :=
  option.cases_on (M.f (name.to_idx a) (name.to_idx b)) 0 (λ aff,
    if h : bF = yG ∧ yF = bG then begin
      rcases h with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      have fg := to_process_space (concretion.pseudo_apply.quotient F G),
      from aff • (fg - to_process_space A - to_process_space B),
    end else 0)

/-- Show that the interaction tensor worker is commutitive. -/
private lemma interaction_tensor_worker.comm {M : affinity ℍ}
  : ∀ (A B : quotient (@species.setoid ℍ ω (context.extend M.arity context.nil))
           × (Σ' (b y), quotient (@concretion.setoid ℍ ω (context.extend M.arity context.nil) b y))
           × name (context.extend M.arity context.nil))
  , interaction_tensor_worker M A B = interaction_tensor_worker M B A
| ⟨ A, ⟨ bF, yF, F ⟩, a ⟩ ⟨ B, ⟨ bG, yG, G ⟩, b ⟩ := begin
  simp only [interaction_tensor_worker],
  have : M.f (name.to_idx a) (name.to_idx b) = M.f (name.to_idx b) (name.to_idx a)
       := M.symm _ _,
  rw this,

  cases M.f (name.to_idx b) (name.to_idx a),
  case option.none { from rfl },
  case option.some {
    simp only [],
    by_cases this : (bF = yG ∧ yF = bG),
    {
      rcases this with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      let h : bF = bF ∧ yF = yF := ⟨ rfl, rfl ⟩,
      let g : yF = yF ∧ bF = bF := ⟨ rfl, rfl ⟩,
      simp only [dif_pos h, dif_pos g, concretion.psuedo_apply.quotient.symm],
      simp only [fin_fn.sub_eq_add_neg, add_comm, add_left_comm],
    },
    {
      have h : ¬ (bG = yF ∧ yG = bF),
      { rintros ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩, from this ⟨ rfl, rfl ⟩ },
      simp only [dif_neg this, dif_neg h],
    }
  }
end

/-- Compute the interaction tensor between two elements in the interaction
    space. -/
noncomputable def interaction_tensor {M : affinity ℍ}
  : interaction_space ℍ ω (context.extend M.arity context.nil)
  → interaction_space ℍ ω (context.extend M.arity context.nil)
  → process_space ℍ ω (context.extend M.arity context.nil)
| x y := fin_fn.bind₂ x y (interaction_tensor_worker M)

infix ` ⊘ `:73 := interaction_tensor

lemma interaction_tensor.zero_left {M : affinity ℍ}
  : ∀ (A : interaction_space ℍ ω (context.extend M.arity context.nil))
  , A ⊘ 0 = 0
| A := fin_fn.bind₂_zero_left A _

lemma interaction_tensor.zero_right {M : affinity ℍ}
  : ∀ (A : interaction_space ℍ ω (context.extend M.arity context.nil))
  , 0 ⊘ A = 0
| A := fin_fn.bind₂_zero_right A _

lemma interaction_tensor.comm {M : affinity ℍ}
    (A B : interaction_space ℍ ω (context.extend M.arity context.nil))
  : A ⊘ B = B ⊘ A := begin
  suffices : (λ x y, interaction_tensor_worker M x y)
           = (λ x y, interaction_tensor_worker M y x),
  { show fin_fn.bind₂ A B (interaction_tensor_worker M)
       = fin_fn.bind₂ B A (λ x y, interaction_tensor_worker M x y),
    -- Sneaky use of η-expanding one function to make sure the rewrite applies.
    rw this,
    from fin_fn.bind₂_swap A B (interaction_tensor_worker M) },

  from funext (λ x, funext (interaction_tensor_worker.comm x)),
end

lemma interaction_tensor.left_distrib {M : affinity ℍ}
    (A B C : interaction_space ℍ ω (context.extend M.arity context.nil))
  : (A + B) ⊘ C = A ⊘ C + B ⊘ C
  := by simp only [interaction_tensor, fin_fn.bind₂, fin_fn.bind_distrib]

lemma interaction_tensor.right_distrib {M : affinity ℍ}
    (A B C : interaction_space ℍ ω (context.extend M.arity context.nil))
  : A ⊘ (B + C) = A ⊘ B + A ⊘ C
  := calc  A ⊘ (B + C)
         = (B + C) ⊘ A : interaction_tensor.comm A _
     ... = B ⊘ A + C ⊘ A : interaction_tensor.left_distrib B C A
     ... = A ⊘ B + A ⊘ C : by rw [interaction_tensor.comm B, interaction_tensor.comm C]

end cpi

#lint-
