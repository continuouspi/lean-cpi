import data.cpi.process data.cpi.transition
import data.multiset2

namespace cpi
/-- Given two equivalent species, there is some isomorphism between species of
    the same  kind and label, such that isomorphic transitions have equivalent
    productions. -/
@[nolint has_inhabited_instance]
def has_iso {ℍ : Type} {ω Γ : context} [∀ Γ, setoid (species ℍ ω Γ)] [∀ Γ b y, setoid (concretion ℍ ω Γ b y)]
    {A B : species ℍ ω Γ} (ℓ : lookup ℍ ω Γ)
  : A ≈ B → Type
| c := ∀ k (α : label ℍ Γ k)
       , Σ' (iso : (Σ E, A [ℓ, α]⟶ E) ≃ (Σ E, B [ℓ, α]⟶ E))
         , ∀ E (t : A [ℓ, α]⟶ E), E ≈ (iso.to_fun ⟨ E, t ⟩).1

/-- An equivalence class over species and concretions, which allows for a notion of "prime
    decomposition". -/
class cpi_equiv (ℍ : Type) (ω : context) :=
  [species_equiv {} : ∀ Γ, setoid (species ℍ ω Γ)]
  [concretion_equiv {} : ∀ Γ b y, setoid (concretion ℍ ω Γ b y)]
  [decide_species {} : ∀ Γ, decidable_rel (species_equiv Γ).r]
  [decide_concretion {} : ∀ Γ b y, decidable_rel (concretion_equiv Γ b y).r]

  /- Decompose a species into primes. -/
  (prime_decompose {Γ} : species ℍ ω Γ → multiset (prime_species ℍ ω Γ))

  ( prime_decompose_equiv {Γ} {A B : species ℍ ω Γ}
  : A ≈ B
  → multiset.map quotient.mk (prime_decompose A)
  = multiset.map quotient.mk (prime_decompose B) )

  /- Prime decomposition of nil, returns an empty set. -/
  (prime_decompose_nil {Γ} : prime_decompose (@species.nil ℍ ω Γ) = 0)

  ( prime_decompose_parallel {Γ} (A B : species ℍ ω Γ)
  : prime_decompose (A |ₛ B) = prime_decompose A + prime_decompose B )

  ( prime_decompose_prime {Γ} (A : prime_species ℍ ω Γ)
  : prime_decompose A.val = [ A ])

  ( pseudo_apply {Γ} {a b : ℕ}
  : concretion' ℍ ω Γ a b → concretion' ℍ ω Γ b a
  → species' ℍ ω Γ )

namespace cpi_equiv
  instance to_species (ℍ : Type) (ω Γ : context) [r : cpi_equiv ℍ ω]
    : setoid (species ℍ ω Γ)
    := species_equiv Γ

  instance to_concretion (ℍ : Type) (ω Γ : context) (b y : ℕ) [r : cpi_equiv ℍ ω]
    : setoid (concretion ℍ ω Γ b y)
    := concretion_equiv Γ b y

  variables {ℍ : Type} {ω : context} [cpi_equiv ℍ ω]

  /-- `prime_decompose` lifted to quotients. -/
  def prime_decompose' {Γ} :
    species' ℍ ω Γ → multiset (prime_species' ℍ ω Γ)
  | A := quot.lift_on A (multiset.map quotient.mk ∘ prime_decompose)
    (λ A B eq, prime_decompose_equiv eq)

  lemma prime_decompose_nil' {Γ} : prime_decompose' ⟦ @species.nil ℍ ω Γ ⟧ = 0 := begin
      show multiset.map quotient.mk (prime_decompose nil) = 0,
      rw [prime_decompose_nil, multiset.map_zero],
    end

  lemma prime_decompose_parallel' {Γ} (A B : species ℍ ω Γ)
    : prime_decompose' ⟦ A |ₛ B ⟧ = prime_decompose' ⟦ A ⟧ + prime_decompose' ⟦ B ⟧
    := begin
      show multiset.map quotient.mk (prime_decompose (A |ₛ B))
         = multiset.map quotient.mk (prime_decompose A)
         + multiset.map quotient.mk (prime_decompose B),
      rw [prime_decompose_parallel, multiset.map_add],
    end

  lemma prime_decompose_prime' {Γ} (A : prime_species' ℍ ω Γ)
    : prime_decompose' (prime_species.unwrap A) = [ A ]
    := quot.rec_on A (λ A, begin
      show multiset.map quotient.mk (prime_decompose A.val) = [ ⟦ A ⟧ ],
      simp only [prime_decompose_prime, multiset.coe_map, list.map_nil, multiset.coe_eq_coe, list.map],
    end) (λ a b _, rfl)
end cpi_equiv

/-- Additional properties that we need for some lemmas, but nothing else./ -/
class cpi_equiv_prop (ℍ : Type) (ω : context) extends cpi_equiv ℍ ω :=
  /- Show our equivalence relation holds over transitions. Namely the transition
     sets are isomorphic, and have equivalent productions. -/
  ( transition_iso {Γ} (ℓ : lookup ℍ ω Γ) {A B : species ℍ ω Γ} (eq : A ≈ B)
  : nonempty (has_iso ℓ eq) )

  ( pseudo_apply_symm {Γ} {a b : ℕ} (F : concretion' ℍ ω Γ a b) (G : concretion' ℍ ω Γ b a)
    : pseudo_apply F G = pseudo_apply G F )

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

end cpi

#lint-
