import data.cpi.semantics.relation
import data.fin_fn algebra.half_ring

namespace cpi

/-- Determine if two concretions are equal. Effectively a decision procedure for
    structural congruence. -/
instance concretion_wrap.decidable_eq {ℍ ω Γ} [cpi_equiv ℍ ω] :
  decidable_eq ( prime_species' ℍ ω Γ
               × (Σ (b y : ℕ), concretion' ℍ ω Γ b y) × name Γ)
| a b := by apply_instance

/-- A vector-space representation of processes, mapping prime species into their
    concentrations. -/
@[nolint has_inhabited_instance]
def process_space (ℂ ℍ : Type) (ω Γ : context) [add_monoid ℂ] [cpi_equiv ℍ ω]
  := fin_fn (prime_species' ℍ ω Γ) ℂ

variables {ℂ ℍ : Type} {ω : context} [half_ring ℂ] [cpi_equiv ℍ ω] [decidable_eq ℂ]

instance process_space.add_comm_monoid {Γ} : add_comm_group (process_space ℂ ℍ ω Γ) := fin_fn.add_comm_group _ ℂ
instance process_space.semimodule {Γ} : semimodule ℂ (process_space ℂ ℍ ω Γ) := fin_fn.semimodule _ ℂ
instance process_space.has_repr {ℂ} [add_monoid ℂ] [has_repr ℂ] {Γ} [has_repr (species' ℍ ω Γ)]
  : has_repr (process_space ℂ ℍ ω Γ) := ⟨ fin_fn.to_string "\n" ⟩

/-- Convert a species into a process space with a unit vector for each element
    of the prime decomposition.

    This is defined as ⟨A⟩ within the paper. -/
def to_process_space {Γ} (A : species' ℍ ω Γ) : process_space ℂ ℍ ω Γ
  := (cpi_equiv.prime_decompose' A).sum' (λ A, fin_fn.single A 1)

@[simp]
lemma to_process_space.nil {Γ} : to_process_space ⟦nil⟧ = (0 : process_space ℂ ℍ ω Γ)
  := by simp only [to_process_space, cpi_equiv.prime_decompose_nil', multiset.sum'_zero]

@[simp]
lemma to_process_space.prime {Γ} (A : prime_species' ℍ ω Γ)
  : (to_process_space (prime_species.unwrap A) : process_space ℂ ℍ ω Γ)
  = fin_fn.single A 1
  := by simp only [to_process_space, cpi_equiv.prime_decompose_prime', multiset.sum'_singleton]

@[simp]
lemma to_process_space.parallel {Γ} (A B : species ℍ ω Γ)
  : (to_process_space ⟦ A |ₛ B ⟧ : process_space ℂ ℍ ω Γ)
  = to_process_space ⟦ A ⟧ + to_process_space ⟦ B ⟧
  := by simp only [to_process_space, cpi_equiv.prime_decompose_parallel', multiset.sum'_add]

/-- The vector space (A, E, a)→ℍ relating transitions from A to E with label #a.
  -/
@[nolint has_inhabited_instance]
def interaction_space (ℂ ℍ : Type) (ω Γ : context) [add_monoid ℂ] [cpi_equiv ℍ ω] : Type
  := fin_fn
      ( prime_species' ℍ ω Γ
      × (Σ (b y), concretion' ℍ ω Γ b y)
      × name Γ)
      ℂ

instance interaction_space.add_comm_monoid {Γ} : add_comm_group (interaction_space ℂ ℍ ω Γ) := fin_fn.add_comm_group _ ℂ
instance interaction_space.semimodule {Γ} : semimodule ℂ (interaction_space ℂ ℍ ω Γ) := fin_fn.semimodule _ ℂ

instance interaction_space.has_repr {ℂ} [add_monoid ℂ] [has_repr ℂ] {Γ}
  [has_repr (species' ℍ ω Γ)] [∀ b y, has_repr (concretion' ℍ ω Γ b y)]
  : has_repr (interaction_space ℂ ℍ ω Γ) := ⟨ @fin_fn.to_string
    ( prime_species' ℍ ω Γ
      × (Σ (b y), concretion' ℍ ω Γ b y)
      × name Γ) ℂ _
    ⟨ λ ⟨ A, ⟨ _, _, F ⟩, a ⟩, "[" ++ repr A ++ "], [" ++ repr F ++ "], " ++ repr a ⟩
    _ "\n" ⟩

/-- Convert a process into a process space. -/
def process.to_space {Γ}
  : process ℂ ℍ ω Γ → process_space ℂ ℍ ω Γ
| (c ◯ A) := c • to_process_space ⟦ A ⟧
| (P |ₚ Q) := process.to_space P + process.to_space Q

/-- Convert a process space into a process. -/
def process.from_space {ℂ} [add_comm_monoid ℂ] {Γ} : process_space ℂ ℍ ω Γ → process' ℂ ℍ ω Γ
| Ps := process.from_prime_multiset Ps.space Ps.support.val

/-- Convert a class of equivalent processes into a process space. -/
def process.to_space' {Γ} : process' ℂ ℍ ω Γ → process_space ℂ ℍ ω Γ
| P := quot.lift_on P process.to_space (λ P Q eq, begin
  induction eq,
  case process.equiv.refl { from rfl },
  case process.equiv.trans : P Q R _ _ pq qr { from trans pq qr },
  case process.equiv.symm : P Q _ ih { from symm ih },

  case process.equiv.ξ_species : c A A' eq {
    simp only [process.to_space, quotient.sound eq],
  },
  case process.equiv.ξ_parallel₁ : P P' Q _ ih { simp only [process.to_space, ih] },
  case process.equiv.ξ_parallel₂ : P Q Q' _ ih { simp only [process.to_space, ih] },

  case process.equiv.parallel_nil : P c {
    simp only [process.to_space, cpi.to_process_space.nil, smul_zero, add_zero],
  },
  case process.equiv.parallel_symm { simp only [process.to_space, add_comm] },
  case process.equiv.parallel_assoc { simp only [process.to_space, add_assoc] },
  case cpi.process.equiv.join : A c d { simp only [process.to_space, add_smul] },
  case cpi.process.equiv.split : A B c {
    simp only [process.to_space, to_process_space.parallel, smul_add],
  }
end)

axiom process.from_inverse {Γ} :
  function.left_inverse process.to_space' (@process.from_space ℍ ω _ ℂ _ Γ)

/-- Show that process spaces can be embeeded into equivalence classes of processes. -/
def process.space_embed {Γ} : process_space ℂ ℍ ω Γ ↪ process' ℂ ℍ ω Γ :=
  { to_fun := process.from_space,
    inj := function.injective_of_left_inverse process.from_inverse }

end cpi

#lint-
