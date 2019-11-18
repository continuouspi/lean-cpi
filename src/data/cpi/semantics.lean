import data.cpi.species data.cpi.concretion data.cpi.process data.cpi.transition
import data.fin_fn

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

noncomputable instance process_space.has_neg {ω Γ} : has_neg (process_space ω Γ)
  := fin_fn.has_neg _ ℝ

noncomputable instance process_space.has_sub {ω Γ} : has_sub (process_space ω Γ)
  := fin_fn.has_sub _ ℝ

noncomputable instance process_space.has_scalar {ω Γ} : has_scalar ℝ (process_space ω Γ)
  := fin_fn.has_scalar _ ℝ

/-- Convert a single prime species into a process space. This returns one when
    the process is present, and 0 otherwise. -/
private noncomputable def to_process_space_of {Γ} (A : prime_species' ω Γ) : process_space ω Γ
  := { space := λ B, decidable.cases_on (classical.dec (A = B)) (λ _, 0) (λ _, 1),
       defined := finset.singleton A,
       defined_if := λ B nZero, begin
        cases (classical.dec (A = B)),
        case decidable.is_false { by contradiction },
        case decidable.is_true { from finset.mem_singleton.mpr (symm h) }
       end }

/-- Map elements together and sum them. -/
def sum_map {α β : Type} [add_comm_monoid β] (f : α → β) (xs : quotient (list.is_setoid α)) : β
  := quot.lift_on xs
    (list.foldr (λ x s, f x + s) 0)
    (λ a b p, begin
      induction p,
      case list.perm.nil { from rfl },
      case list.perm.skip : A l₁ l₂ eq ih { unfold list.foldr, rw ih },
      case list.perm.swap : A B l { simp only [add_comm, list.foldr, add_left_comm] },
      case list.perm.trans : l₁ l₂ l₃ ab bc ihab ihbc { from trans ihab ihbc },
    end)

/-- Convert a species into a process space. This computes the prime
    decomposition, and then converts it to a process space. -/
noncomputable def to_process_space {Γ} (A : multiset (prime_species' ω Γ)) : process_space ω Γ
  := sum_map to_process_space_of A

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

noncomputable instance interaction_space.has_scalar {ω Γ} : has_scalar ℝ (interaction_space ω Γ)
  := fin_fn.has_scalar _ ℝ

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
| ⟨ _, # a , @production.concretion _ _ b y G, tr ⟩ :=
  { space := λ B, decidable.cases_on (classical.dec (B = ⟨ ⟦ A ⟧, ⟨ b, y, ⟦ G ⟧ ⟩, a ⟩)) (λ _, 0) (λ _, 1),
    defined := finset.singleton ⟨ ⟦ A ⟧, ⟨ b, y, ⟦ G ⟧ ⟩, a ⟩,
    defined_if := λ B nZero, begin
      cases (classical.dec (B = ⟨ ⟦ A ⟧, ⟨ b, y, ⟦ G ⟧ ⟩, a ⟩)),
      case decidable.is_false { by contradiction },
      case decidable.is_true { from finset.mem_singleton.mpr h }
    end }
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
  c.val • sum_map potential_interaction_space transitions.elems.val
| (P |ₚ Q) := process_potential P + process_potential Q

noncomputable def process_immediate
    (M : affinity) (ℓ : lookup ω (context.extend M.arity context.nil))
  : process ω (context.extend M.arity context.nil)
  → process_space ω (context.extend M.arity context.nil)
| (c ◯ A) :=
  let transitions := transition.enumerate ℓ A in
  c.val • sum_map immediate_process_space transitions.elems.val
  + 0.5 • interaction_tensor M (process_potential M ℓ (c ◯ A)) (process_potential M ℓ (c ◯ A))
| (P |ₚ Q)
  := process_immediate P + process_immediate Q
   + interaction_tensor M (process_potential M ℓ P) (process_potential M ℓ Q)

end cpi

#lint
