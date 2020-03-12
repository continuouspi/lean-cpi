import data.cpi.semantics.space tactic.abel

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
lemma interaction_tensor.left_distrib [cpi_equiv ℍ ω]
    (A B C : interaction_space ℂ ℍ ω (context.extend M.arity context.nil))
  : (A + B) ⊘[conc] C = A ⊘[conc] C + B ⊘[conc] C
  := by simp only [interaction_tensor, fin_fn.bind₂, fin_fn.bind_distrib]

@[simp]
lemma interaction_tensor.right_distrib [cpi_equiv_prop ℍ ω]
    (A B C : interaction_space ℂ ℍ ω (context.extend M.arity context.nil))
  : A ⊘[conc] (B + C) = A ⊘[conc] B + A ⊘[conc] C
  := calc  A ⊘ (B + C)
         = (B + C) ⊘ A : interaction_tensor.comm A _
     ... = B ⊘ A + C ⊘ A : interaction_tensor.left_distrib B C A
     ... = A ⊘ B + A ⊘ C : by rw [interaction_tensor.comm B, interaction_tensor.comm C]


lemma interaction_tensor.smul [cpi_equiv_prop ℍ ω]
    (c : ℂ) (A B : interaction_space ℂ ℍ ω (context.extend M.arity context.nil))
  : c • (A ⊘[conc] B) = (c • A) ⊘[conc] B
  := fin_fn.bind_smul c A _

lemma interaction_tensor.ext_single [cpi_equiv_prop ℍ ω] {bF yF}
    (A B : species' ℍ ω (context.extend M.arity context.nil))
    (F F' : concretion' ℍ ω (context.extend M.arity context.nil) bF yF)
    (a : name (context.extend M.arity context.nil)) (c : ℂ)
  : (∀ G, ( to_process_space (cpi_equiv.pseudo_apply F G) - to_process_space A
          : process_space ℂ ℍ ω (context.extend M.arity context.nil) )
        = to_process_space (cpi_equiv.pseudo_apply F' G) - to_process_space B)
  → ∀ (ξ : interaction_space ℂ ℍ ω (context.extend M.arity context.nil))
  , fin_fn.single ( A, (⟨ bF, yF, F ⟩ : (Σ' (b y), concretion' ℍ ω (context.extend M.arity context.nil) b y)), a ) c
    ⊘[conc] ξ
  = fin_fn.single ( B, ⟨bF, ⟨ yF, F' ⟩ ⟩, a ) c ⊘[conc] ξ
| f ξ := begin
  simp only [interaction_tensor, fin_fn.bind₂, fin_fn.bind_single],
  suffices : fin_fn.bind ξ (interaction_tensor_worker conc (A, ⟨bF, yF, F⟩, a))
           = fin_fn.bind ξ (interaction_tensor_worker conc (B, ⟨bF, yF, F'⟩, a)),
    from congr_arg _ this,

  suffices : ∀ x, interaction_tensor_worker conc (A, ⟨bF, yF, F⟩, a) x
                = interaction_tensor_worker conc (B, ⟨bF, yF, F'⟩, a) x,
  { have h := funext this, simp only at h, rw h },

  rintros ⟨ C, ⟨ bG, yG, G ⟩, b' ⟩,
  simp only [interaction_tensor_worker],
  cases (M.f (name.to_idx a) (name.to_idx b')); simp only [],
  by_cases is_eq : (bF = yG ∧ yF = bG),
  {
    simp only [dif_pos is_eq], rcases is_eq with ⟨ l, r ⟩, subst l, subst r, simp only [],
    rw f G,
  },
  { simp only [dif_neg is_eq] },
end

lemma interaction_tensor.parallel₁ [cpi_equiv_prop ℍ ω]
    (A B : species ℍ ω (context.extend M.arity context.nil))
    {bF yF} (F : concretion ℍ ω (context.extend M.arity context.nil) bF yF)
    (a : name (context.extend M.arity context.nil)) (c : ℂ)
  : ∀ (ξ : interaction_space ℂ ℍ ω (context.extend M.arity context.nil))
  , fin_fn.single ( ⟦A |ₛ B⟧, (⟨ bF, yF, ⟦ F |₁ B ⟧ ⟩ : (Σ' (b y), concretion' ℍ ω (context.extend M.arity context.nil) b y)), a ) c
    ⊘[conc] ξ
  = fin_fn.single ( ⟦ A ⟧, ⟨bF, ⟨ yF, ⟦ F ⟧ ⟩ ⟩, a ) c ⊘[conc] ξ
  := interaction_tensor.ext_single ⟦ A |ₛ B ⟧ ⟦ A ⟧ ⟦ F |₁ B ⟧ ⟦ F ⟧ a c (λ G, begin
  have : ( to_process_space (cpi_equiv.pseudo_apply ⟦F |₁ B⟧ G)
         : process_space ℂ ℍ ω _ )
       = to_process_space (cpi_equiv.pseudo_apply ⟦F⟧ G) + to_process_space ⟦ B ⟧,
  {
    unfold to_process_space,
    rw cpi_equiv_prop.pseudo₁,
    simp only [multiset.map_add, multiset.sum_add],
  },
  rw [this, to_process_space.parallel], abel,
end)

lemma interaction_tensor.parallel₂ [cpi_equiv_prop ℍ ω]
    (A B : species ℍ ω (context.extend M.arity context.nil))
    {bF yF} (F : concretion ℍ ω (context.extend M.arity context.nil) bF yF)
    (a : name (context.extend M.arity context.nil)) (c : ℂ)
  : ∀ (ξ : interaction_space ℂ ℍ ω (context.extend M.arity context.nil))
  , fin_fn.single ( ⟦A |ₛ B⟧, (⟨ bF, yF, ⟦ A |₂ F ⟧ ⟩ : (Σ' (b y), concretion' ℍ ω (context.extend M.arity context.nil) b y)), a ) c
    ⊘[conc] ξ
  = fin_fn.single ( ⟦ B ⟧, ⟨bF, ⟨ yF, ⟦ F ⟧ ⟩ ⟩, a ) c ⊘[conc] ξ
  := interaction_tensor.ext_single ⟦ A |ₛ B ⟧ ⟦ B ⟧ ⟦ A |₂ F ⟧ ⟦ F ⟧ a c (λ G, begin
  have : ( to_process_space (cpi_equiv.pseudo_apply ⟦ A |₂ F ⟧ G)
         : process_space ℂ ℍ ω _ )
       = to_process_space ⟦ A ⟧ + to_process_space (cpi_equiv.pseudo_apply ⟦F⟧ G),
  {
    unfold to_process_space,
    rw cpi_equiv_prop.pseudo₂,
    simp only [multiset.map_add, multiset.sum_add],
  },
  rw [this, to_process_space.parallel], abel,
end)

instance interaction_tensor.monoid_hom_left [cpi_equiv_prop ℍ ω]
    (ξ : interaction_space ℂ ℍ ω (context.extend M.arity context.nil))
  : is_add_monoid_hom (interaction_tensor conc ξ)
  := { map_add := interaction_tensor.right_distrib ξ,
       map_zero := interaction_tensor.zero_left ξ }

end cpi

#lint-
