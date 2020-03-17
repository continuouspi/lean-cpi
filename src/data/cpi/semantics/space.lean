import data.cpi.process data.cpi.transition
import data.fin_fn data.multiset2 algebra.half_ring

namespace cpi

/-- Given two equivalent species, there is some isomorphism between species of
    the same  kind and label, such that isomorphic transitions have equivalent
    productions. -/
@[nolint has_inhabited_instance]
def has_iso {ℍ : Type} {ω Γ : context} [∀ Γ, setoid (species ℍ ω Γ)] [∀ Γ b y, setoid (concretion ℍ ω Γ b y)]
    {A B : species ℍ ω Γ} (ℓ : lookup ℍ ω Γ)
  : A ≈ B → Type
| c := ∀ k (α : label ℍ Γ k)
       , Σ' (iso : (Σ' E, A [ℓ, α]⟶ E) ≃ (Σ' E, B [ℓ, α]⟶ E))
         , ∀ E (t : A [ℓ, α]⟶ E), E ≈ (iso.to_fun ⟨ E, t ⟩).1

/-- An equivalence class over species and concretions, which allows for a notion of "prime
    decomposition". -/
class cpi_equiv (ℍ : Type) (ω : context) :=
  [species_equiv {} : ∀ Γ, setoid (species ℍ ω Γ)]
  [concretion_equiv {} : ∀ Γ b y, setoid (concretion ℍ ω Γ b y)]
  [decide_species {} : ∀ Γ, decidable_rel (species_equiv Γ).r]
  [decide_concretion {} : ∀ Γ b y, decidable_rel (concretion_equiv Γ b y).r]

  /- Decompose a species into primes. -/
  (prime_decompose {Γ} : species' ℍ ω Γ → multiset (prime_species' ℍ ω Γ))

  /- Prime decomposition of nil, returns an empty set. -/
  (prime_decompose_nil {Γ} : prime_decompose ⟦@species.nil ℍ ω Γ⟧ = 0)

  ( prime_decompose_parallel {Γ} (A B : species ℍ ω Γ)
  : prime_decompose ⟦A |ₛ B⟧ = prime_decompose ⟦ A ⟧ + prime_decompose ⟦ B ⟧ )

  ( prime_decompose_prime {Γ} (A : prime_species' ℍ ω Γ)
  : prime_decompose (prime_species.unwrap A) = [ A ] )

  ( pseudo_apply {Γ} {a b : ℕ}
  : concretion' ℍ ω Γ a b → concretion' ℍ ω Γ b a
  → species' ℍ ω Γ )

/-- Additional properties that we need for some lemmas, but nothing else./ -/
class cpi_equiv_prop (ℍ : Type) (ω : context) extends cpi_equiv ℍ ω :=
  /- Show our equivalence relation holds over transitions. Namely the transition
     sets are isomorphic, and have equivalent productions. -/
  ( transition_iso {Γ} (ℓ : lookup ℍ ω Γ) {A B : species ℍ ω Γ} (eq : A ≈ B)
  : nonempty (has_iso ℓ eq) )

  ( pseudo_apply_symm {Γ} {a b : ℕ} (F : concretion' ℍ ω Γ a b) (G : concretion' ℍ ω Γ b a)
    : pseudo_apply F G = pseudo_apply G F )

  /- More intuitively stated as (F|A)∘G ≈ (F∘G)|A, but this is annoying to do
     given our abstraction. -/
  ( pseudo₁ {Γ} {a b : ℕ}
    (A : species ℍ ω Γ) (F : concretion ℍ ω Γ a b) (G : concretion' ℍ ω Γ b a)
    : prime_decompose (pseudo_apply ⟦F |₁ A⟧ G)
    = prime_decompose (pseudo_apply ⟦ F ⟧ G ) + prime_decompose ⟦ A ⟧)

  ( pseudo₂ {Γ} {a b : ℕ}
    (A : species ℍ ω Γ) (F : concretion ℍ ω Γ a b) (G : concretion' ℍ ω Γ b a)
    : prime_decompose (pseudo_apply ⟦A |₂ F⟧ G)
    = prime_decompose ⟦ A ⟧ + prime_decompose (pseudo_apply ⟦ F ⟧ G ) )

instance cpi_equiv.to_species (ℍ : Type) (ω Γ : context) [r : cpi_equiv ℍ ω]
  : setoid (species ℍ ω Γ)
  := cpi_equiv.species_equiv Γ

instance cpi_equiv.to_concretion (ℍ : Type) (ω Γ : context) (b y : ℕ) [r : cpi_equiv ℍ ω]
  : setoid (concretion ℍ ω Γ b y)
  := cpi_equiv.concretion_equiv Γ b y

/-- Build an equivalent transition in the forward direction. -/
def cpi_equiv.transition_from_fwd {ℍ : Type} {ω Γ : context} [r : cpi_equiv ℍ ω] {A B : species ℍ ω Γ}
    {ℓ : lookup ℍ ω Γ} {eq : A ≈ B}
  : has_iso ℓ eq
  → transition.transition_from ℓ A → transition.transition_from ℓ B
| iso ⟨ k, α, p ⟩ := ⟨ k, α, (iso k α).1.to_fun p ⟩

/-- Build an equivalent transition in the reverse direction. -/
def cpi_equiv.transition_from_inv {ℍ : Type} {ω Γ : context} [r : cpi_equiv ℍ ω] {A B : species ℍ ω Γ}
    {ℓ : lookup ℍ ω Γ} {eq : A ≈ B}
  : has_iso ℓ eq
  → transition.transition_from ℓ B → transition.transition_from ℓ A
| iso ⟨ k, α, p ⟩ := ⟨ k, α, (iso k α).1.inv_fun p ⟩

/-- cpi_equiv.transition_iso, lifted to transition_from -/
def cpi_equiv_prop.transition_from_iso {ℍ : Type} {ω Γ : context} [r : cpi_equiv ℍ ω] {A B : species ℍ ω Γ}
    {ℓ : lookup ℍ ω Γ} {eq : A ≈ B}
  : has_iso ℓ eq
  → transition.transition_from ℓ A ≃ transition.transition_from ℓ B
| iso :=
  { to_fun    := cpi_equiv.transition_from_fwd iso,
    inv_fun   := cpi_equiv.transition_from_inv iso,
    left_inv  := λ ⟨ k, α, p ⟩, begin
      simp only [cpi_equiv.transition_from_fwd, cpi_equiv.transition_from_inv],
      rw (iso k α).1.left_inv p
    end,
    right_inv := λ ⟨ k, α, p ⟩, begin
      simp only [cpi_equiv.transition_from_fwd, cpi_equiv.transition_from_inv],
      rw (iso k α).1.right_inv p
    end }

instance species'.decidable_eq {ℍ ω Γ} [r : cpi_equiv ℍ ω] : decidable_eq (species' ℍ ω Γ)
  := @quotient.decidable_eq _ _ (cpi_equiv.decide_species Γ)

instance concretion'.decidable_eq {ℍ ω Γ b y} [r : cpi_equiv ℍ ω] : decidable_eq (concretion' ℍ ω Γ b y)
  := @quotient.decidable_eq _ _ (cpi_equiv.decide_concretion Γ b y)

/-- Determine if two prime species are equal. Effectively a decision procedure
    structural congruence. -/
instance prime'.decidable_eq {ℍ ω Γ} [r : cpi_equiv ℍ ω] : decidable_eq (prime_species' ℍ ω Γ)
| A B := quotient.rec_on_subsingleton₂ A B
  (λ ⟨ a, _ ⟩ ⟨ b, _ ⟩,
    match cpi_equiv.decide_species Γ a b with
    | is_true h := is_true (quot.sound h)
    | is_false h := is_false (λ h', absurd (quotient.exact h') h)
    end)

/-- Determine if two concretions are equal. Effectively a decision procedure for
    structural congruence. -/
instance concretion_wrap.decidable_eq {ℍ ω Γ} [cpi_equiv ℍ ω] :
  decidable_eq ( species' ℍ ω Γ
               × (Σ' (b y : ℕ), concretion' ℍ ω Γ b y) × name Γ)
| ⟨ A, ⟨ a, x, F ⟩, e ⟩ ⟨ B, ⟨ b, y, G ⟩, f ⟩ := by apply_instance

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
  := multiset.sum (multiset.map (λ A, fin_fn.single A 1) (cpi_equiv.prime_decompose A))

@[simp]
lemma to_process_space.nil {Γ} : to_process_space ⟦nil⟧ = (0 : process_space ℂ ℍ ω Γ) := begin
  unfold to_process_space,
  rw cpi_equiv.prime_decompose_nil,
  simp only [multiset.sum_zero, multiset.map_zero],
end

lemma to_process_space.prime {Γ} (A : prime_species' ℍ ω Γ)
  : (to_process_space (prime_species.unwrap A) : process_space ℂ ℍ ω Γ)
  = fin_fn.single A 1 := begin
  unfold to_process_space,
  rw cpi_equiv.prime_decompose_prime,
  -- Not the best way, but the easiest.
  simp only [list.sum_cons, multiset.coe_map, add_zero,
    list.sum_nil, pi.add_apply, pi.zero_apply, list.map_nil, multiset.coe_sum,
    list.map_cons],
end

lemma to_process_space.parallel {Γ} (A B : species ℍ ω Γ)
  : (to_process_space ⟦ A |ₛ B ⟧ : process_space ℂ ℍ ω Γ)
  = to_process_space ⟦ A ⟧ + to_process_space ⟦ B ⟧ := begin
  unfold to_process_space,
  rw cpi_equiv.prime_decompose_parallel A B,
  simp only [multiset.map_add, multiset.sum_add],
end

/-- The vector space (A, E, a)→ℍ relating transitions from A to E with label #a.
  -/
@[nolint has_inhabited_instance]
def interaction_space (ℂ ℍ : Type) (ω Γ : context) [add_monoid ℂ] [cpi_equiv ℍ ω] : Type
  := fin_fn
      ( species' ℍ ω Γ
      × (Σ' (b y), concretion' ℍ ω Γ b y)
      × name Γ)
      ℂ

instance interaction_space.add_comm_monoid {Γ} : add_comm_group (interaction_space ℂ ℍ ω Γ) := fin_fn.add_comm_group _ ℂ
instance interaction_space.semimodule {Γ} : semimodule ℂ (interaction_space ℂ ℍ ω Γ) := fin_fn.semimodule _ ℂ

instance interaction_space.has_repr {ℂ} [add_monoid ℂ] [has_repr ℂ] {Γ}
  [has_repr (species' ℍ ω Γ)] [∀ b y, has_repr (concretion' ℍ ω Γ b y)]
  : has_repr (interaction_space ℂ ℍ ω Γ) := ⟨ @fin_fn.to_string
    ( species' ℍ ω Γ
      × (Σ' (b y), concretion' ℍ ω Γ b y)
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
| P := begin
  refine quot.lift_on P process.to_space _,
  assume P Q eq,
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
end

axiom process.from_inverse {Γ} :
  function.left_inverse process.to_space' (@process.from_space ℍ ω _ ℂ _ Γ)

/-- Show that process spaces can be embeeded into equivalence classes of processes. -/
def process.space_embed {Γ} : process_space ℂ ℍ ω Γ ↪ process' ℂ ℍ ω Γ :=
  { to_fun := process.from_space,
    inj := function.injective_of_left_inverse process.from_inverse }

end cpi

#lint-
