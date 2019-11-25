import data.cpi.process data.cpi.transition
import data.fin_fn data.multiset2 tactic.abel

namespace cpi

/-- A quotient of all structurally congruent species. -/
def species' (ℍ : Type) (ω Γ : context) := quotient (@species.setoid ℍ ω Γ)

/-- A quotient of all structurally congruent species which are prime. -/
def prime_species' (ℍ : Type) (ω Γ : context) := quotient (@prime_species.setoid ℍ ω Γ)


def process_space (ℍ : Type) (ω Γ : context) [add_monoid ℍ] := fin_fn (prime_species' ℍ ω Γ) ℍ

variables {ℍ : Type} {ω : context} [linear_ordered_field ℍ] [decidable_eq ℍ]

-- Oh no. We make use of lots of non-computable things at this point, so I'm
-- afraid I gave up.
--
-- Right now, I just want to show things work (for some definition of the word),
-- and then fill in the many gaps.

private noncomputable def prime_equal {Γ} :
  decidable_eq (prime_species' ℍ ω Γ) := classical.dec_eq _

private noncomputable def concretion_equal {Γ} :
  decidable_eq ( quotient (@species.setoid ℍ ω Γ)
               × (Σ' (b y : ℕ), quotient (@concretion.setoid ℍ ω Γ b y)) × name Γ)
  := classical.dec_eq _

local attribute [instance] prime_equal concretion_equal

-- instance process_space.has_zero {ω Γ} : has_zero (process_space ω Γ)
--   := by { unfold process_space, apply_instance }
noncomputable instance process_space.add_comm_monoid {ω Γ} : add_comm_monoid (process_space ℍ ω Γ)
  := fin_fn.add_comm_monoid _ ℍ

instance process_space.has_neg {ω Γ} : has_neg (process_space ℍ ω Γ)
  := fin_fn.has_neg _ ℍ

noncomputable instance process_space.has_sub {ω Γ} : has_sub (process_space ℍ ω Γ)
  := fin_fn.has_sub _ ℍ

noncomputable instance process_space.distrib_mul_action {ω Γ} : distrib_mul_action ℍ (process_space ℍ ω Γ)
  := fin_fn.distrib_mul_action _ ℍ

/-- Convert a single prime species into a process space. This returns one when
    the process is present, and 0 otherwise. -/
private noncomputable def to_process_space_of {Γ} (A : prime_species' ℍ ω Γ) : process_space ℍ ω Γ
  := fin_fn.mk_basis A

/-- Convert a species into a process space. This computes the prime
    decomposition, and then converts it to a process space. -/
noncomputable def to_process_space {Γ} (A : multiset (prime_species' ℍ ω Γ)) : process_space ℍ ω Γ
  := multiset.sum_map to_process_space_of A

-- TODO: Show that this satisfies the required function.

def interaction_space (ℍ : Type) (ω Γ : context) [add_monoid ℍ] : Type
  := fin_fn
      ( quotient (@species.setoid ℍ ω Γ)
      × (Σ' (b y), quotient (@concretion.setoid ℍ ω Γ b y))
      × name Γ)
      ℍ

noncomputable instance interaction_space.add_comm_monoid {Γ}
  : add_comm_monoid (interaction_space ℍ ω Γ)
  := fin_fn.add_comm_monoid _ ℍ

noncomputable instance interaction_space.has_sub {ω Γ} : has_sub (interaction_space ℍ ω Γ)
  := fin_fn.has_sub _ ℍ

noncomputable instance interaction_space.distrib_mul_action {ω Γ} : distrib_mul_action ℍ (interaction_space ℍ ω Γ)
  := fin_fn.distrib_mul_action _ ℍ

constant do_prime_decompose :
  ∀ {Γ}, species' ℍ ω Γ → multiset (quotient (@prime_species.setoid ℍ ω Γ))

noncomputable def to_process_space' {Γ} (A : species' ℍ ω Γ)
  : process_space ℍ ω Γ
  := to_process_space (do_prime_decompose A)

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
    if h : bF = yG ∧ yF = bG then
      let to_space := λ x,
        @to_process_space' ℍ ω _ _ (context.extend M.arity context.nil) x in
      begin
        rcases h with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
        have fg := to_space (concretion.pseudo_apply.quotient F G),
        from aff • (fg - to_space A - to_space B),
      end
    else 0)

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

lemma interaction_tensor.distrib {M : affinity ℍ}
    (A B C : interaction_space ℍ ω (context.extend M.arity context.nil))
  : (A + B) ⊘ C = A ⊘ C + B ⊘ C
  := by simp only [interaction_tensor, fin_fn.bind₂, fin_fn.bind_distrib]

/-- Maps a potential transition to the interaction space. -/
private noncomputable def potential_interaction_space {Γ} {ℓ : lookup ℍ ω Γ} {A : species ℍ ω Γ}
  : transition.transition_from ℓ A
  → interaction_space ℍ ω Γ
| ⟨ _, # a , @production.concretion _ _ _ b y G, tr ⟩ := fin_fn.mk_basis ⟨ ⟦ A ⟧, ⟨ b, y, ⟦ G ⟧ ⟩, a ⟩
| ⟨ _, τ@'_, E, tr ⟩ := 0
| ⟨ _, τ⟨_⟩, E, tr ⟩ := 0

private lemma potential_interaction_space.equiv
  {Γ} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ} :
  ∀ {k} {α : label ℍ Γ k} {E E' : production ℍ ω Γ k}
    {t : A [ℓ, α]⟶ E} {t' : B [ℓ, α]⟶ E'}
  , A ≈ B → E ≈ E'
  → potential_interaction_space (transition.transition_from.mk t)
  = potential_interaction_space (transition.transition_from.mk t')
| _ (# a) (@production.concretion _ _ _ b y E) (production.concretion E') t t' eqA (production.equiv.concretion eqE) := begin
  unfold transition.transition_from.mk potential_interaction_space,
  have : ⟦ A ⟧ = ⟦ B ⟧ := quot.sound eqA,
  have : ⟦ E ⟧ = ⟦ E' ⟧ := quot.sound eqE,
  rw [‹⟦ A ⟧ = ⟦ B ⟧›, ‹⟦ E ⟧ = ⟦ E' ⟧›],
end
| _ (τ@'_) E E' t t' _ _ := rfl
| _ (τ⟨_⟩) E E' t t' _ _ := rfl

/-- Maps a spontanious/immediate transition to a process space. -/
private noncomputable def immediate_process_space
    {M : affinity ℍ} {ℓ : lookup ℍ ω (context.extend M.arity context.nil)} {A : species ℍ ω (context.extend M.arity context.nil)}
  : transition.transition_from ℓ A
  → process_space ℍ ω (context.extend M.arity context.nil)
| ⟨ _, # a , _, tr ⟩ := 0
| ⟨ _, τ@'k, production.species B, tr ⟩ :=
  k • (to_process_space' ⟦ B ⟧ - to_process_space' ⟦ A ⟧)
| ⟨ _, τ⟨ n ⟩, production.species B, tr ⟩ :=
  let arity := quot.lift_on n
    (λ ⟨ a, b ⟩, M.f (name.to_idx a) (name.to_idx b))
    (λ ⟨ a₁, b₁ ⟩ ⟨ a₂, b₂ ⟩ eq, begin
      rcases eq with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩ | ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      from rfl,
      from M.symm (name.to_idx a₁) (name.to_idx b₁),
    end) in
  option.cases_on arity 0 (λ k, k • (to_process_space' ⟦ B ⟧ - to_process_space' ⟦ A ⟧))

private lemma immediate_process_space.equiv
    {M : affinity ℍ} {ℓ : lookup ℍ ω (context.extend M.arity context.nil)}
    {A B : species ℍ ω (context.extend M.arity context.nil)}
  : ∀ {k} {α : label ℍ (context.extend M.arity context.nil) k}
      {E E' : production ℍ ω (context.extend M.arity context.nil) k}
      {t : A [ℓ, α]⟶ E} {t' : B [ℓ, α]⟶ E'}
    , A ≈ B → E ≈ E'
    → immediate_process_space (transition.transition_from.mk t)
    = immediate_process_space (transition.transition_from.mk t')
| _ (# a ) E E' t t' eqA eqE := rfl
| _ (τ@'k) (production.species E) (production.species E') t t' eqA (production.equiv.species eqE) := begin
  unfold transition.transition_from.mk immediate_process_space,
  have : ⟦ A ⟧ = ⟦ B ⟧ := quot.sound eqA,
  have : ⟦ E ⟧ = ⟦ E' ⟧ := quot.sound eqE,
  rw [‹⟦ A ⟧ = ⟦ B ⟧›, ‹⟦ E ⟧ = ⟦ E' ⟧›],
end
| _ (τ⟨ n ⟩) (production.species E) (production.species E') t t' eqA (production.equiv.species eqE) := begin
  unfold transition.transition_from.mk immediate_process_space,
  have : ⟦ A ⟧ = ⟦ B ⟧ := quot.sound eqA,
  have : ⟦ E ⟧ = ⟦ E' ⟧ := quot.sound eqE,
  rw [‹⟦ A ⟧ = ⟦ B ⟧›, ‹⟦ E ⟧ = ⟦ E' ⟧›],
end

/-- The vector space of potential interactions of a process. -/
noncomputable def process_potential
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
  : process ℍ ω (context.extend M.arity context.nil)
  → interaction_space ℍ ω (context.extend M.arity context.nil)
| (c ◯ A) :=
  let transitions := transition.enumerate ℓ A in
  c • multiset.sum_map potential_interaction_space transitions.elems.val
| (P |ₚ Q) := process_potential P + process_potential Q


lemma process_potential.nil_zero
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
    (c : ℍ)
  : process_potential M ℓ (c ◯ nil) = 0 := begin
  simp only [process_potential],
  generalize : transition.enumerate ℓ nil = As,
  rcases As with ⟨ ⟨ As, nodup ⟩, elems ⟩,

  -- We have that there are no possible transitions, and thus the sum is 0.
  have : As = 0 := multiset.eq_zero_of_forall_not_mem (λ ⟨ k, α, E, t ⟩, by cases t),
  simp only [‹ As = 0 ›, multiset.sum_map, multiset.fold_zero, multiset.map_zero,
             smul_zero],
end

noncomputable def process_immediate
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
  : process ℍ ω (context.extend M.arity context.nil)
  → process_space ℍ ω (context.extend M.arity context.nil)
| (c ◯ A) :=
  let transitions := transition.enumerate ℓ A in
  c • multiset.sum_map immediate_process_space transitions.elems.val
  + ((1 : ℍ) / 2) • (process_potential M ℓ (c ◯ A) ⊘ process_potential M ℓ (c ◯ A))
| (P |ₚ Q)
  := process_immediate P + process_immediate Q
   + (process_potential M ℓ P ⊘ process_potential M ℓ Q)

lemma process_immediate.nil_zero
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
    (c : ℍ)
  : process_immediate M ℓ (c ◯ nil) = 0 := begin
  simp only [process_immediate],

  have : process_potential M ℓ (c ◯ nil) = 0 := process_potential.nil_zero M ℓ c,
  rw [this],

  generalize : transition.enumerate ℓ nil = As,
  rcases As with ⟨ ⟨ As, nodup ⟩, elems ⟩,

  -- We have that there are no possible transitions, and thus the sum is 0.
  have : As = 0 := multiset.eq_zero_of_forall_not_mem (λ ⟨ k, α, E, t ⟩, by cases t),
  simp only [‹ As = 0 ›, multiset.sum_map, multiset.fold_zero, multiset.map_zero,
             interaction_tensor.zero_left, smul_zero, add_zero],
end

lemma process_potential.equiv
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
  : ∀ {P Q : process ℍ ω (context.extend M.arity context.nil)}
  , P ≈ Q → process_potential M ℓ P = process_potential M ℓ Q
| P Q eq := begin
  induction eq,
  case process.equiv.refl { refl },
  case process.equiv.trans : P Q R ab bc ih_ab ih_bc { from trans ih_ab ih_bc },
  case process.equiv.symm : P Q eq ih { from symm ih },
  case process.equiv.ξ_species : c A B eq {
    simp only [process_potential],

    cases eq,
    generalize : transition.enumerate ℓ A = As,
    generalize : transition.enumerate ℓ B = Bs,

    suffices
      : multiset.sum_map potential_interaction_space As.elems.val
      = multiset.sum_map potential_interaction_space Bs.elems.val,
      from congr_arg (has_scalar.smul c) this,

    suffices : ∀ x
      , potential_interaction_space x
      = potential_interaction_space ((transition.equivalent_of.is_equiv eq).to_fun x),
      let iso := transition.equivalent_of.is_equiv eq,
      from multiset.sum_map_iso
        potential_interaction_space potential_interaction_space iso this
        As.elems Bs.elems
        (λ x _, @fintype.complete _ Bs (iso.to_fun x))
        (λ x _, @fintype.complete _ As (iso.inv_fun x)),

    rintros ⟨ k, α, E, t ⟩,
    simp only [transition.equivalent_of.is_equiv, transition.equivalent_of.transition_from],
    rcases (transition.equivalent_of eq t) with ⟨ E', eqE, t' ⟩,
    from potential_interaction_space.equiv ⟨ eq ⟩ eqE,
  },
  case process.equiv.ξ_parallel₁ : P P' Q eq ih {
    unfold process_potential, rw ih,
  },
  case process.equiv.ξ_parallel₂ : P Q Q' eq ih {
    unfold process_potential, rw ih,
  },
  case process.equiv.parallel_nil : P C {
    unfold1 process_potential,
    show process_potential M ℓ P + process_potential M ℓ (C ◯ nil) = process_potential M ℓ P,

    have : process_potential M ℓ (C ◯ nil) = 0 := process_potential.nil_zero M ℓ C,
    simp only [this, add_zero],
  },
  case cpi.process.equiv.parallel_symm { simp only [process_potential, add_comm] },
  case process.equiv.parallel_assoc { simp only [process_potential, add_assoc] },
  case process.equiv.join : A c d {
    simp only [process_potential],
    from eq.symm (fin_fn.add_smul c d _),
  }
end

private lemma process_immediate.join {M : affinity ℍ} (c d : ℍ)
    (Ds : interaction_space ℍ ω (context.extend (M.arity) context.nil))
    (Ps : process_space ℍ ω (context.extend (M.arity) context.nil))
  : (c • Ds) ⊘ (d • Ds) + (((1 : ℍ) / 2) • (c • Ds) ⊘ (c • Ds) + ((1 : ℍ) / 2) • (d • Ds) ⊘ (d • Ds))
  = ((1 : ℍ) / 2) • (c • Ds + d • Ds) ⊘ (c • Ds + d • Ds) := begin
  rw [interaction_tensor.distrib (c • Ds) (d • Ds),
      interaction_tensor.comm _ (c • Ds + d • Ds),
      interaction_tensor.comm _ (c • Ds + d • Ds),
      interaction_tensor.distrib (c • Ds) (d • Ds),
      interaction_tensor.distrib (c • Ds) (d • Ds)],

  simp only [smul_add],
  generalize ehalf : (1 : ℍ) / 2 = half,

  from calc  (c • Ds) ⊘ (d • Ds)
           + (half • (c • Ds) ⊘ (c • Ds) + half • (d • Ds) ⊘ (d • Ds))

           = (1 : ℍ) • (c • Ds) ⊘ (d • Ds)
           + (half • (c • Ds) ⊘ (c • Ds) + half • (d • Ds) ⊘ (d • Ds))
           : by simp only [one_smul]

       ... = (half + half) • (c • Ds) ⊘ (d • Ds)
           + (half • (c • Ds) ⊘ (c • Ds) + half • (d • Ds) ⊘ (d • Ds))
           : by rw [← add_halves (1 : ℍ), ← ehalf]

       ... = half • (c • Ds) ⊘ (c • Ds) + half • (c • Ds) ⊘ (d • Ds)
           + (half • (c • Ds) ⊘ (d • Ds) + half • (d • Ds) ⊘ (d • Ds))
           : begin
             simp only [fin_fn.add_smul],
             generalize : half • (c • Ds) ⊘ (d • Ds) = cd,
             generalize : half • (c • Ds) ⊘ (c • Ds) = cc,
             generalize : half • (d • Ds) ⊘ (d • Ds) = dd,
             abel,
           end

       ... = half • (c • Ds) ⊘ (c • Ds) + half • (d • Ds) ⊘ (c • Ds)
           + (half • (c • Ds) ⊘ (d • Ds) + half • (d • Ds) ⊘ (d • Ds))
           : by simp only [interaction_tensor.comm],
end

lemma process_immediate.equiv
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
  : ∀ {P Q : process ℍ ω (context.extend M.arity context.nil)}
  , P ≈ Q → process_immediate M ℓ P = process_immediate M ℓ Q
| P Q eq := begin
  induction eq,
  case process.equiv.refl { from rfl },
  case process.equiv.symm : A B eq ih { from (symm ih) },
  case process.equiv.trans : P Q R ab bc ih_ab ih_bc { from trans ih_ab ih_bc },

  case process.equiv.ξ_species : c A B eq {
    simp only [process_immediate],

    generalize : transition.enumerate ℓ A = As,
    generalize : transition.enumerate ℓ B = Bs,

    suffices : multiset.sum_map immediate_process_space As.elems.val
             = multiset.sum_map immediate_process_space Bs.elems.val,
    { have eql : process_potential M ℓ (c ◯ A) = process_potential M ℓ (c ◯ B)
        := process_potential.equiv M ℓ (process.equiv.ξ_species eq),
      rw [this, eql] },

    cases eq,
    suffices : ∀ x
      , immediate_process_space x
      = immediate_process_space ((transition.equivalent_of.is_equiv eq).to_fun x),
      let iso := transition.equivalent_of.is_equiv eq,
      from multiset.sum_map_iso
        immediate_process_space immediate_process_space iso this
        As.elems Bs.elems
        (λ x _, @fintype.complete _ Bs (iso.to_fun x))
        (λ x _, @fintype.complete _ As (iso.inv_fun x)),

    rintros ⟨ k, α, E, t ⟩,
    simp only [transition.equivalent_of.is_equiv, transition.equivalent_of.transition_from],
    rcases (transition.equivalent_of eq t) with ⟨ E', eqE, t' ⟩,
    from immediate_process_space.equiv ⟨ eq ⟩ eqE,
  },
  case process.equiv.ξ_parallel₁ : P P' Q eq ih {
    unfold process_immediate,
    rw [process_potential.equiv M ℓ eq, ih],
  },
  case process.equiv.ξ_parallel₂ : P Q Q' eq ih {
    unfold process_immediate,
    rw [process_potential.equiv M ℓ eq, ih],
  },
  case process.equiv.parallel_nil {
    simp only [process_immediate, process_immediate.nil_zero, add_zero,
               process_potential.nil_zero, interaction_tensor.zero_left],
  },
  case cpi.process.equiv.parallel_symm : P Q {
    simp only [process_immediate, add_comm, interaction_tensor.comm],
  },
  case process.equiv.parallel_assoc : P Q R {
    simp only [process_immediate, add_assoc] ,
    simp only [add_left_comm],
    refine congr_arg _ _,
    refine congr_arg _ _,
    refine congr_arg _ _,

    unfold process_potential,

    generalize : process_potential M ℓ P = p,
    generalize : process_potential M ℓ Q = q,
    generalize : process_potential M ℓ R = r,

    from calc  p ⊘ q + (p + q) ⊘ r
             = p ⊘ q + p ⊘ r + q ⊘ r : by rw [interaction_tensor.distrib, add_assoc]
         ... = q ⊘ r + q ⊘ p + r ⊘ p : by simp only [add_comm, add_left_comm, interaction_tensor.comm]
         ... = q ⊘ r + (q + r) ⊘ p : by rw [add_assoc, ← interaction_tensor.distrib]
         ... = q ⊘ r + p ⊘ (q + r) : by rw [interaction_tensor.comm _ p]
  },
  case process.equiv.join : A c d {
    simp only [process_immediate, process_potential],

    generalize : multiset.sum_map potential_interaction_space ((fintype.elems (transition.transition_from ℓ A)).val) = Ds,
    generalize : multiset.sum_map immediate_process_space ((fintype.elems (transition.transition_from ℓ A)).val) = Ps,

    suffices
      : (c • Ds) ⊘ (d • Ds) + (((1 : ℍ) / 2) • ((c • Ds) ⊘ (c • Ds)) + ((1 : ℍ) / 2) • (d • Ds) ⊘ (d • Ds))
      = ((1 : ℍ) / 2) • ((c • Ds + d • Ds) ⊘ (c • Ds + d • Ds)),
      { simp only [add_assoc, add_comm, fin_fn.add_smul, add_left_comm, this] },

    from process_immediate.join c d Ds Ps,

  }
end

end cpi

#lint
