import data.cpi.process data.cpi.transition
import data.fin_fn data.multiset2

namespace cpi

variable {ω : context}

def species' (ω Γ : context) := quotient (@species.setoid ω Γ)
def prime_species' (ω Γ : context) := quotient (@prime_species.setoid ω Γ)

def process_space (ω Γ : context) := fin_fn (prime_species' ω Γ) ℝ

-- Oh no. We make use of lots of non-computable things at this point, so I'm
-- afraid I gave up.
--
-- Right now, I just want to show things work (for some definition of the word),
-- and then fill in the many gaps.
local attribute [instance] classical.prop_decidable

-- instance process_space.has_zero {ω Γ} : has_zero (process_space ω Γ)
--   := by { unfold process_space, apply_instance }
noncomputable instance process_space.add_comm_monoid {ω Γ} : add_comm_monoid (process_space ω Γ)
  := fin_fn.add_comm_monoid _ ℝ

instance process_space.has_neg {ω Γ} : has_neg (process_space ω Γ)
  := fin_fn.has_neg _ ℝ

noncomputable instance process_space.has_sub {ω Γ} : has_sub (process_space ω Γ)
  := fin_fn.has_sub _ ℝ

noncomputable instance process_space.distrib_mul_action {ω Γ} : distrib_mul_action ℝ (process_space ω Γ)
  := fin_fn.distrib_mul_action _ ℝ

/-- Convert a single prime species into a process space. This returns one when
    the process is present, and 0 otherwise. -/
private noncomputable def to_process_space_of {Γ} (A : prime_species' ω Γ) : process_space ω Γ
  := fin_fn.mk_basis A -- TODO: Convert to use species equality.


/-- Convert a species into a process space. This computes the prime
    decomposition, and then converts it to a process space. -/
noncomputable def to_process_space {Γ} (A : multiset (prime_species' ω Γ)) : process_space ω Γ
  := multiset.sum_map to_process_space_of A

-- TODO: Show that this satisfies the required function.

def interaction_space (ω Γ : context) : Type
  := fin_fn
      ( quotient (@species.setoid ω Γ)
      × (Σ' (b y), quotient (@concretion.setoid ω Γ b y))
      × name Γ)
      ℝ

noncomputable instance interaction_space.add_comm_monoid {ω Γ}
  : add_comm_monoid (interaction_space ω Γ)
  := fin_fn.add_comm_monoid _ ℝ

noncomputable instance interaction_space.has_sub {ω Γ} : has_sub (interaction_space ω Γ)
  := fin_fn.has_sub _ ℝ

noncomputable instance interaction_space.distrib_mul_action {ω Γ} : distrib_mul_action ℝ (interaction_space ω Γ)
  := fin_fn.distrib_mul_action _ ℝ

constant do_prime_decompose :
  ∀ {Γ}, species' ω Γ → multiset (quotient (@prime_species.setoid ω Γ))

noncomputable def to_process_space' {Γ} (A : species' ω Γ)
  : process_space ω Γ
  := to_process_space (do_prime_decompose A)

/-- Compute the interaction tensor between two elements in the interaction
    space. -/
noncomputable def interaction_tensor (M : affinity)
  : interaction_space ω (context.extend M.arity context.nil)
  → interaction_space ω (context.extend M.arity context.nil)
  → process_space ω (context.extend M.arity context.nil)
| x y := fin_fn.bind₂ x y (λ ⟨ A, ⟨ bF, yF, F ⟩, a ⟩ ⟨ B, ⟨ bG, yG, G ⟩, b ⟩,
  match M.f (name.to_idx a) (name.to_idx b) with
  | option.none := 0
  | option.some aff :=
    if h : bF = yG ∧ yF = bG then
      let to_space := λ x,
        @to_process_space' ω (context.extend M.arity context.nil) x in
      begin
        rcases h with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
        have fg := to_space (concretion.pseudo_apply.quotient F G),
        from aff.val • (fg - to_space A - to_space B),
      end
    else 0
  end)

private noncomputable def potential_interaction_space {Γ} {ℓ : lookup ω Γ} {A : species ω Γ}
  : transition.transition_from ℓ A
  → interaction_space ω Γ
| ⟨ _, # a , @production.concretion _ _ b y G, tr ⟩ := fin_fn.mk_basis ⟨ ⟦ A ⟧, ⟨ b, y, ⟦ G ⟧ ⟩, a ⟩
| ⟨ _, τ@'_, E, tr ⟩ := 0
| ⟨ _, τ⟨_⟩, E, tr ⟩ := 0

private noncomputable def immediate_process_space
    {M : affinity} {ℓ : lookup ω (context.extend M.arity context.nil)} {A : species ω (context.extend M.arity context.nil)}
  : transition.transition_from ℓ A
  → process_space ω (context.extend M.arity context.nil)
| ⟨ _, # a , _, tr ⟩ := 0
| ⟨ _, τ@'k, production.species B, tr ⟩ :=
  k.val • (to_process_space' ⟦ B ⟧ - to_process_space' ⟦ A ⟧)
| ⟨ _, τ⟨ n ⟩, production.species B, tr ⟩ :=
  let arity := quot.lift_on n
    (λ ⟨ a, b ⟩, M.f (name.to_idx a) (name.to_idx b))
    (λ ⟨ a₁, b₁ ⟩ ⟨ a₂, b₂ ⟩ eq, begin
      rcases eq with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩ | ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      from rfl,
      from M.symm (name.to_idx a₁) (name.to_idx b₁),
    end) in
  match arity with
  | none := 0
  | some k := k.val • (to_process_space' ⟦ B ⟧ - to_process_space' ⟦ A ⟧)
  end

/-- The vector space of potential interactions of a process. -/
noncomputable def process_potential
    (M : affinity) (ℓ : lookup ω (context.extend M.arity context.nil))
  : process ω (context.extend M.arity context.nil)
  → interaction_space ω (context.extend M.arity context.nil)
| (c ◯ A) :=
  let transitions := transition.enumerate ℓ A in
  c.val • multiset.sum_map potential_interaction_space transitions.elems.val
| (P |ₚ Q) := process_potential P + process_potential Q

noncomputable def process_immediate
    (M : affinity) (ℓ : lookup ω (context.extend M.arity context.nil))
  : process ω (context.extend M.arity context.nil)
  → process_space ω (context.extend M.arity context.nil)
| (c ◯ A) :=
  let transitions := transition.enumerate ℓ A in
  c.val • multiset.sum_map immediate_process_space transitions.elems.val
  + 0.5 • interaction_tensor M (process_potential M ℓ (c ◯ A)) (process_potential M ℓ (c ◯ A))
| (P |ₚ Q)
  := process_immediate P + process_immediate Q
   + interaction_tensor M (process_potential M ℓ P) (process_potential M ℓ Q)

lemma potential_interaction_space.equiv
  {Γ} {ℓ : lookup ω Γ} {A B : species ω Γ} :
  ∀ {k} {α : label Γ k} {E E' : production ω Γ k}
    {t : A [ℓ, α]⟶ E} {t' : B [ℓ, α]⟶ E'}
  , A ≈ B → E ≈ E'
  → potential_interaction_space ⟨k, α, E, t⟩
  = potential_interaction_space ⟨k, α, E', t'⟩
| _ (# a) (@production.concretion _ _ b y E) (production.concretion E') t t' eqA (production.equiv.concretion eqE) := begin
  unfold potential_interaction_space,
  have : ⟦ A ⟧ = ⟦ B ⟧ := quot.sound eqA,
  have : ⟦ E ⟧ = ⟦ E' ⟧ := quot.sound eqE,
  rw [‹⟦ A ⟧ = ⟦ B ⟧›, ‹⟦ E ⟧ = ⟦ E' ⟧›],
end
| _ (τ@'_) E E' t t' _ _ := rfl
| _ (τ⟨_⟩) E E' t t' _ _ := rfl

lemma process_potential.equiv
    (M : affinity) (ℓ : lookup ω (context.extend M.arity context.nil))
  : ∀ (P Q : process ω (context.extend M.arity context.nil))
  , P ≈ Q → process_potential M ℓ P = process_potential M ℓ Q
| P Q eq := begin
  induction eq,
  case process.equiv.refl { refl },
  case process.equiv.trans : P Q R ab bc ih_ab ih_bc { from trans ih_ab ih_bc },
  case process.equiv.symm : P Q eq ih { from symm ih },
  case process.equiv.ξ_species : c A B eq {
    simp only [process_potential],

    cases eq,
    let iso := transition.equivalent_of.is_equiv eq,
    generalize : transition.enumerate ℓ A = As,
    generalize : transition.enumerate ℓ B = Bs,

    suffices
      : multiset.sum_map potential_interaction_space As.elems.val
      = multiset.sum_map potential_interaction_space Bs.elems.val,
      from congr_arg (has_scalar.smul c.val) this,

    suffices : ∀ x
      , potential_interaction_space x
      = potential_interaction_space ((transition.equivalent_of.is_equiv eq).to_fun x),
      from multiset.sum_map.iso_equal
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
    simp only [process_potential],

    generalize : transition.enumerate ℓ nil = As,
    show process_potential M ℓ P
         + C.val • multiset.sum_map potential_interaction_space As.elems.val
       = process_potential M ℓ P,
    rcases As with ⟨ ⟨ As, nodup ⟩, elems ⟩,
    simp only [],
    have : As = 0 := multiset.eq_zero_of_forall_not_mem (λ ⟨ k, α, E, t ⟩, by cases t),
    subst ‹ As = 0 ›,

    simp only [multiset.sum_map, multiset.foldr_zero],
    have : (@has_scalar.smul real (interaction_space ω _) _ C.val 0) = 0 := smul_zero C.val,
    rw this,
    simp only [add_zero],
  },
  case cpi.process.equiv.parallel_symm { simp only [process_potential, add_comm] },
  case process.equiv.parallel_assoc { simp only [process_potential, add_assoc] },
  case process.equiv.join : A c d {
    simp only [process_potential],
    from eq.symm (fin_fn.smul_add c d _),
  }
end

end cpi

#lint
