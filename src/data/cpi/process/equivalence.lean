import data.cpi.species data.cpi.process.basic

namespace cpi
namespace process

variables {ℂ ℍ : Type} {ω Γ : context} [has_add ℂ] [∀ Γ, setoid (species ℍ ω Γ)]

/-- Structural congruence of processes. -/
inductive equiv : process ℂ ℍ ω Γ → process ℂ ℍ ω Γ → Prop
| refl  {A}     : equiv A A
| trans {A B C} : equiv A B → equiv B C → equiv A C
| symm  {A B}   : equiv A B → equiv B A

-- Projection
| ξ_species   {c : ℂ} {A B} : A ≈ B → equiv (c ◯ A) (c ◯ B)
| ξ_parallel₁ {P P' Q} : equiv P P' → equiv (P |ₚ Q) (P' |ₚ Q)
| ξ_parallel₂ {P Q Q'} : equiv Q Q' → equiv (P |ₚ Q) (P |ₚ Q')

-- Monoidic properties
| parallel_nil   {P} {c : ℂ} : equiv (P |ₚ c ◯ species.nil) P
| parallel_symm  {P Q} : equiv (P |ₚ Q) (Q |ₚ P)
| parallel_assoc {P Q R} : equiv ((P |ₚ Q) |ₚ R) (P |ₚ (Q |ₚ R))

-- Join identical species together.
| join  {A} {c d} : equiv (c ◯ A |ₚ d ◯ A) ((c + d) ◯ A)

instance : is_equiv (process ℂ ℍ ω Γ) equiv :=
  { refl := @equiv.refl _ _ _ _ _ _, symm := @equiv.symm _ _ _ _ _ _, trans := @equiv.trans _ _ _ _ _ _ }
instance : is_refl (process ℂ ℍ ω Γ) equiv := ⟨ λ _, equiv.refl ⟩
instance : setoid (process ℂ ℍ ω Γ) :=
  ⟨ equiv, ⟨ @equiv.refl _ _ _ _ _ _, @equiv.symm _ _ _ _ _ _, @equiv.trans _ _ _ _ _ _ ⟩ ⟩
instance setoid.is_equiv : is_equiv (process ℂ ℍ ω Γ) has_equiv.equiv :=
  process.is_equiv

namespace equiv
  lemma parallel_symm₁ {P Q R : process ℂ ℍ ω Γ} : (P |ₚ Q |ₚ R) ≈ (Q |ₚ P |ₚ R) :=
    calc  (P |ₚ (Q |ₚ R))
        ≈ ((P |ₚ Q) |ₚ R) : symm parallel_assoc
    ... ≈ ((Q |ₚ P) |ₚ R) : ξ_parallel₁ parallel_symm
    ... ≈ (Q |ₚ (P |ₚ R)) : parallel_assoc

  lemma parallel_symm₂ {P Q R : process ℂ ℍ ω Γ} : ((P |ₚ Q) |ₚ R) ≈ ((P |ₚ R) |ₚ Q) :=
    calc  ((P |ₚ Q) |ₚ R)
        ≈ (P |ₚ (Q |ₚ R)) : parallel_assoc
    ... ≈ (P |ₚ (R |ₚ Q)) : ξ_parallel₂ parallel_symm
    ... ≈ ((P |ₚ R) |ₚ Q) : symm parallel_assoc
end equiv

namespace parallel.quot
  /-- Make a parallel process from a quotient of two process. -/
  def mk : quotient (@process.setoid ℂ ℍ ω Γ _ _) → quotient (@process.setoid ℂ ℍ ω Γ _ _) → quotient (@process.setoid ℂ ℍ ω Γ _ _)
  | A B := quotient.lift_on₂ A B (λ A B, ⟦ A |ₚ B ⟧)
      (λ A B A' B' eqA eqB, quot.sound (trans (equiv.ξ_parallel₁ eqA) ((equiv.ξ_parallel₂ eqB))))

  lemma assoc (A B C : quotient (@process.setoid ℂ ℍ ω Γ _ _))
    : mk A (mk B C) = mk (mk A B) C
    := begin
      rcases quot.exists_rep A with ⟨ A, ⟨ _ ⟩ ⟩,
      rcases quot.exists_rep B with ⟨ B, ⟨ _ ⟩ ⟩,
      rcases quot.exists_rep C with ⟨ C, ⟨ _ ⟩ ⟩,
      from quot.sound (symm equiv.parallel_assoc),
    end
end parallel.quot

/-- Structural congruence of processes, with the extension of c∘(A|B) ≡⁺ c∘A || c∘B  -/
inductive equiv2 : process ℂ ℍ ω Γ → process ℂ ℍ ω Γ → Prop
| refl  {A}     : equiv2 A A
| trans {A B C} : equiv2 A B → equiv2 B C → equiv2 A C
| symm  {A B}   : equiv2 A B → equiv2 B A

-- Projection
| ξ_species   {c : ℂ} {A B} : A ≈ B → equiv2 (c ◯ A) (c ◯ B)
| ξ_parallel₁ {P P' Q} : equiv2 P P' → equiv2 (P |ₚ Q) (P' |ₚ Q)
| ξ_parallel₂ {P Q Q'} : equiv2 Q Q' → equiv2 (P |ₚ Q) (P |ₚ Q')

-- Monoidic properties
| parallel_nil   {P} {c : ℂ} : equiv2 (P |ₚ c ◯ species.nil) P
| parallel_symm  {P Q} : equiv2 (P |ₚ Q) (Q |ₚ P)
| parallel_assoc {P Q R} : equiv2 ((P |ₚ Q) |ₚ R) (P |ₚ (Q |ₚ R))

-- Join/split processes.
| join  {A} {c d : ℂ} : equiv2 (c ◯ A |ₚ d ◯ A) ((c + d) ◯ A)
| split {A B} {c : ℂ} : equiv2 (c ◯ (A |ₛ B)) (c ◯ A |ₚ c ◯ B)

infix ` ≡⁺ `:50 := equiv2

instance equiv2.is_equiv : is_equiv (process ℂ ℍ ω Γ) equiv2 :=
  { refl := @equiv2.refl _ _ _ _ _ _, symm := @equiv2.symm _ _ _ _ _ _, trans := @equiv2.trans _ _ _ _ _ _ }
instance equiv2.is_refl : is_refl (process ℂ ℍ ω Γ) equiv2 := ⟨ λ _, equiv2.refl ⟩

/-- Wraps ≡⁺ in a setoid. -/
def equiv2.setoid : setoid (process ℂ ℍ ω Γ) :=
  ⟨ equiv2, ⟨ @equiv2.refl _ _ _ _ _ _, @equiv2.symm _ _ _ _ _ _, @equiv2.trans _ _ _ _ _ _ ⟩ ⟩

lemma equiv2.of_equiv : ∀ {P Q : process ℂ ℍ ω Γ}, P ≈ Q → P ≡⁺ Q
| P Q eq := begin
  induction eq,
  case equiv.refl { from equiv2.refl },
  case equiv.symm : P Q _ eq { from equiv2.symm eq },
  case equiv.trans : P Q R _ _ pq qr { from equiv2.trans pq qr },
  case equiv.ξ_species : c A B eq { from equiv2.ξ_species eq },
  case equiv.ξ_parallel₁ : P P' Q _ eq { from equiv2.ξ_parallel₁ eq },
  case equiv.ξ_parallel₂ : P Q Q' _ eq { from equiv2.ξ_parallel₂ eq },
  case equiv.parallel_nil { from equiv2.parallel_nil },
  case equiv.parallel_symm { from equiv2.parallel_symm },
  case equiv.parallel_assoc { from equiv2.parallel_assoc },
  case equiv.join { from equiv2.join },
end

/-- Convert a process' to a process'2. -/
def equiv2.quot_of_equiv : quotient (@process.setoid ℂ ℍ ω Γ _ _) → quotient (@equiv2.setoid ℂ ℍ ω Γ _ _)
| P := quot.lift_on P (@quotient.mk _ equiv2.setoid) (λ P Q r, quot.sound (equiv2.of_equiv r))

end process

/-- A quotient of all structurally congruent processes. -/
@[nolint has_inhabited_instance]
def process' (ℂ ℍ : Type) (ω Γ : context) [has_add ℂ] [∀ {Γ}, setoid (species ℍ ω Γ)]
  := quotient (@process.setoid ℂ ℍ ω Γ _ _)

/-- A quotient of all structurally congruent processes, using ≡⁺ -/
@[nolint has_inhabited_instance]
def process'2 (ℂ ℍ : Type) (ω Γ : context) [has_add ℂ] [∀ {Γ}, setoid (species ℍ ω Γ)]
  := quotient (@process.equiv2.setoid ℂ ℍ ω Γ _ _)

end cpi

#lint-
