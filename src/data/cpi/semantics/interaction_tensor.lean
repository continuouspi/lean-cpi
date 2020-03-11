import data.cpi.semantics.space

namespace cpi

variables {ℂ ℍ : Type} {ω : context} {M : affinity ℍ} {conc : ℍ ↪ ℂ} [half_ring ℂ] [decidable_eq ℂ]

/-- The main body of the interaction tensor. Split out into a separate function
    to make unfolding possible. -/
private def interaction_tensor_worker [cpi_equiv ℍ ω] (conc : ℍ ↪ ℂ)
  : ( species' ℍ ω (context.extend M.arity context.nil)
    × (Σ' (b y), concretion' ℍ ω (context.extend M.arity context.nil) b y)
    × name (context.extend M.arity context.nil))
  → ( species' ℍ ω (context.extend M.arity context.nil)
    × (Σ' (b y), concretion' ℍ ω (context.extend M.arity context.nil) b y)
    × name (context.extend M.arity context.nil))
  → process_space ℂ ℍ ω (context.extend M.arity context.nil)
| ⟨ A, ⟨ bF, yF, F ⟩, a ⟩ ⟨ B, ⟨ bG, yG, G ⟩, b ⟩ :=
  option.cases_on (M.f (name.to_idx a) (name.to_idx b)) 0 (λ aff,
    if h : bF = yG ∧ yF = bG then begin
      rcases h with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      have fg := to_process_space (cpi_equiv.pseudo_apply F G),
      from conc aff • (fg - to_process_space A - to_process_space B),
      assumption,
    end else 0)

/-- Show that the interaction tensor worker is commutitive. -/
private lemma interaction_tensor_worker.comm [cpi_equiv_prop ℍ ω]
  : ∀ (A B : species' ℍ ω (context.extend M.arity context.nil)
           × (Σ' (b y), concretion' ℍ ω (context.extend M.arity context.nil) b y)
           × name (context.extend M.arity context.nil))
  , interaction_tensor_worker conc A B = interaction_tensor_worker conc B A
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
      simp only [dif_pos h, dif_pos g, cpi_equiv_prop.pseudo_apply_symm],
      simp only [sub_eq_add_neg, add_comm, add_left_comm],
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
def interaction_tensor [cpi_equiv ℍ ω] (conc: ℍ ↪ ℂ)
  : interaction_space ℂ ℍ ω (context.extend M.arity context.nil)
  → interaction_space ℂ ℍ ω (context.extend M.arity context.nil)
  → process_space ℂ ℍ ω (context.extend M.arity context.nil)
| x y := fin_fn.bind₂ x y (interaction_tensor_worker conc)

infix ` ⊘ `:73 := interaction_tensor _
notation x ` ⊘[`:73 conc `] ` y:73 := interaction_tensor conc x y

@[simp]
lemma interaction_tensor.zero_left [cpi_equiv ℍ ω]
  : ∀ (A : interaction_space ℂ ℍ ω (context.extend M.arity context.nil))
  , A ⊘[conc] 0 = 0
| A := fin_fn.bind₂_zero_left A _

@[simp]
lemma interaction_tensor.zero_right [cpi_equiv ℍ ω]
  : ∀ (A : interaction_space ℂ ℍ ω (context.extend M.arity context.nil))
  , 0 ⊘[conc] A = 0
| A := fin_fn.bind₂_zero_right A _

lemma interaction_tensor.comm [cpi_equiv_prop ℍ ω]
    (A B : interaction_space ℂ ℍ ω (context.extend M.arity context.nil))
  : A ⊘[conc] B = B ⊘[conc] A := begin
  suffices : (λ x y, interaction_tensor_worker conc x y)
           = (λ x y, interaction_tensor_worker conc y x),
  { show fin_fn.bind₂ A B (interaction_tensor_worker conc)
       = fin_fn.bind₂ B A (λ x y, interaction_tensor_worker conc x y),
    -- Sneaky use of η-expanding one function to make sure the rewrite applies.
    rw this,
    from fin_fn.bind₂_swap A B (interaction_tensor_worker conc) },

  from funext (λ x, funext (interaction_tensor_worker.comm x)),
end

@[simp]
lemma interaction_tensor.left_distrib {M : affinity ℍ} [cpi_equiv ℍ ω]
    (A B C : interaction_space ℂ ℍ ω (context.extend M.arity context.nil))
  : (A + B) ⊘[conc] C = A ⊘[conc] C + B ⊘[conc] C
  := by simp only [interaction_tensor, fin_fn.bind₂, fin_fn.bind_distrib]

@[simp]
lemma interaction_tensor.right_distrib {M : affinity ℍ} [cpi_equiv_prop ℍ ω]
    (A B C : interaction_space ℂ ℍ ω (context.extend M.arity context.nil))
  : A ⊘[conc] (B + C) = A ⊘[conc] B + A ⊘[conc] C
  := calc  A ⊘ (B + C)
         = (B + C) ⊘ A : interaction_tensor.comm A _
     ... = B ⊘ A + C ⊘ A : interaction_tensor.left_distrib B C A
     ... = A ⊘ B + A ⊘ C : by rw [interaction_tensor.comm B, interaction_tensor.comm C]

end cpi

#lint-
