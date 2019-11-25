import data.cpi.process data.cpi.concretion
import data.fin_fn data.multiset2

namespace cpi

/-- A quotient of all structurally congruent species. -/
def species' (ℍ : Type) (ω Γ : context) := quotient (@species.setoid ℍ ω Γ)

/-- A quotient of all structurally congruent species which are prime. -/
def prime_species' (ℍ : Type) (ω Γ : context) := quotient (@prime_species.setoid ℍ ω Γ)

/-- A vector-space representation of processes, mapping prime species into their
    concentrations. -/
def process_space (ℍ : Type) (ω Γ : context) [add_monoid ℍ] := fin_fn (prime_species' ℍ ω Γ) ℍ

-- Oh no. We make use of lots of non-computable things at this point, so I'm
-- afraid I gave up.
--
-- Right now, I just want to show things work (for some definition of the word),
-- and then fill in the many gaps.

/-- Determine if two prime species are equal. Effectively a decision procedure
    structural congruence. -/
noncomputable def prime_equal {ℍ} {ω} {Γ} :
  decidable_eq (prime_species' ℍ ω Γ) := classical.dec_eq _

/-- Determine if two concretions are equal. Effectively a decision procedure for
    structural congruence. -/
noncomputable def concretion_equal {ℍ} {ω} {Γ} :
  decidable_eq ( quotient (@species.setoid ℍ ω Γ)
               × (Σ' (b y : ℕ), quotient (@concretion.setoid ℍ ω Γ b y)) × name Γ)
  := classical.dec_eq _

variables {ℍ : Type} {ω : context} [linear_ordered_field ℍ] [decidable_eq ℍ]
local attribute [instance] prime_equal concretion_equal

-- instance process_space.has_zero {ω Γ} : has_zero (process_space ω Γ)
--   := by { unfold process_space, apply_instance }
noncomputable instance process_space.add_comm_monoid {ω Γ} : add_comm_monoid (process_space ℍ ω Γ)
  := fin_fn.add_comm_monoid _ ℍ

noncomputable instance process_space.has_sub {ω Γ} : has_sub (process_space ℍ ω Γ)
  := fin_fn.has_sub _ ℍ

noncomputable instance process_space.distrib_mul_action {ω Γ} : distrib_mul_action ℍ (process_space ℍ ω Γ)
  := fin_fn.distrib_mul_action _ ℍ

/-- Decompose a species into its multiset of prime species. -/
constant do_prime_decompose :
  ∀ {Γ}, species' ℍ ω Γ → multiset (quotient (@prime_species.setoid ℍ ω Γ))

/-- Convert a species into a process space with a unit vector for each element
    of the prime decomposition.

    This is defined as ⟨A⟩ within the paper. -/
noncomputable def to_process_space {Γ} (A : species' ℍ ω Γ)
  : process_space ℍ ω Γ
  := multiset.sum_map fin_fn.mk_basis  (do_prime_decompose A)

-- TODO: Show that this satisfies the required definitions:
-- ⟨A⟩ = 0
-- ⟨A⟩ = A          when A prime
-- ⟨A|B⟩ = ⟨A⟩ + ⟨B⟩ when A ≠ 0 ≠ B

/-- The vector space (A, E, a)→ℍ relating transitions from A to E with label #a.
  -/
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

end cpi

#lint
