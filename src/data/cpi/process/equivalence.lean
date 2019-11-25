import data.cpi.species data.cpi.process.basic

namespace cpi
namespace process

variables {ℍ : Type} {ω : context} [has_add ℍ]

/-- Structural congruence of processes. -/
inductive equiv {Γ} : process ℍ ω Γ → process ℍ ω Γ → Prop
| refl  {A : process ℍ ω Γ} : equiv A A
| trans {A B C : process ℍ ω Γ} : equiv A B → equiv B C → equiv A C
| symm  {A B : process ℍ ω Γ} : equiv A B → equiv B A

-- Projection
| ξ_species   {c : ℍ} {A B : species ℍ ω Γ} : A ≈ B → equiv (c ◯ A) (c ◯ B)
| ξ_parallel₁ {P P' Q : process ℍ ω Γ} : equiv P P' → equiv (P |ₚ Q) (P' |ₚ Q)
| ξ_parallel₂ {P Q Q' : process ℍ ω Γ} : equiv Q Q' → equiv (P |ₚ Q) (P |ₚ Q')

-- Monoidic properties
| parallel_nil   {P : process ℍ ω Γ} {c : ℍ} : equiv (P |ₚ c ◯ species.nil) P
| parallel_symm  {P Q : process ℍ ω Γ} : equiv (P |ₚ Q) (Q |ₚ P)
| parallel_assoc {P Q R : process ℍ ω Γ} : equiv ((P |ₚ Q) |ₚ R) (P |ₚ (Q |ₚ R))

-- Join identical species together.
| join  {A : species ℍ ω Γ} {c d : ℍ} : equiv (c ◯ A |ₚ d ◯ A) ((c + d) ◯ A)

instance {Γ} : is_equiv (process ℍ ω Γ) equiv :=
  { refl := @equiv.refl _ _ _ Γ, symm := @equiv.symm _ _ _ Γ, trans := @equiv.trans _ _ _ Γ }
instance {Γ} : is_refl (process ℍ ω Γ) equiv := ⟨ λ _, equiv.refl ⟩
instance {Γ} : setoid (process ℍ ω Γ) :=
  ⟨ equiv, ⟨ @equiv.refl _ _ _ Γ, @equiv.symm _ _ _ Γ, @equiv.trans _ _ _ Γ ⟩ ⟩
instance setoid.is_equiv {Γ} : is_equiv (process ℍ ω Γ) has_equiv.equiv :=
  process.is_equiv


/-- Structural congruence of processes. -/
inductive equiv2 {Γ} : process ℍ ω Γ → process ℍ ω Γ → Prop
| refl  {A : process ℍ ω Γ} : equiv2 A A
| trans {A B C : process ℍ ω Γ} : equiv2 A B → equiv2 B C → equiv2 A C
| symm  {A B : process ℍ ω Γ} : equiv2 A B → equiv2 B A

-- Projection
| ξ_species   {c : ℍ} {A B : species ℍ ω Γ} : A ≈ B → equiv2 (c ◯ A) (c ◯ B)
| ξ_parallel₁ {P P' Q : process ℍ ω Γ} : equiv2 P P' → equiv2 (P |ₚ Q) (P' |ₚ Q)
| ξ_parallel₂ {P Q Q' : process ℍ ω Γ} : equiv2 Q Q' → equiv2 (P |ₚ Q) (P |ₚ Q')

-- Monoidic properties
| parallel_nil   {P : process ℍ ω Γ} {c : ℍ} : equiv2 (P |ₚ c ◯ species.nil) P
| parallel_symm  {P Q : process ℍ ω Γ} : equiv2 (P |ₚ Q) (Q |ₚ P)
| parallel_assoc {P Q R : process ℍ ω Γ} : equiv2 ((P |ₚ Q) |ₚ R) (P |ₚ (Q |ₚ R))

-- Join/split processes.
| join  {A : species ℍ ω Γ} {c d : ℍ} : equiv2 (c ◯ A |ₚ d ◯ A) ((c + d) ◯ A)
| split {A B : species ℍ ω Γ} {c : ℍ} : equiv2 (c ◯ (A |ₛ B)) (c ◯ A |ₚ c ◯ B)

instance equiv2.is_equiv {Γ} : is_equiv (process ℍ ω Γ) equiv2 :=
  { refl := @equiv2.refl _ _ _ Γ, symm := @equiv2.symm _ _ _ Γ, trans := @equiv2.trans _ _ _ Γ }
instance equiv2.is_refl {Γ} : is_refl (process ℍ ω Γ) equiv2 := ⟨ λ _, equiv2.refl ⟩
def equiv2.is_setoid {Γ} : setoid (process ℍ ω Γ) :=
  ⟨ equiv2, ⟨ @equiv2.refl _ _ _ Γ, @equiv2.symm _ _ _ Γ, @equiv2.trans _ _ _ Γ ⟩ ⟩

infix ` ≡⁺ `:50 := equiv2

lemma extend_equiv {Γ} : ∀ {P Q : process ℍ ω Γ}, P ≈ Q → P ≡⁺ Q
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

end process
end cpi

#lint
