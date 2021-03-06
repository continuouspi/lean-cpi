import data.cpi.concretion.basic

namespace cpi
namespace concretion

variables {ℍ : Type} {ω : context} [∀ Γ, setoid (species ℍ ω Γ)]

/-- Structural congruence between concretions. -/
inductive equiv : ∀ {Γ} {b y}, concretion ℍ ω Γ b y → concretion ℍ ω Γ b y → Prop
| refl  {Γ} {b y} {F : concretion ℍ ω Γ b y} : equiv F F
| trans {Γ} {b y} {F G H : concretion ℍ ω Γ b y} : equiv F G → equiv G H → equiv F H
| symm  {Γ} {b y} {F G : concretion ℍ ω Γ b y} : equiv F G → equiv G F

| ξ_parallel₁
    {Γ} {b y} {F F' : concretion ℍ ω Γ b y} {A : species ℍ ω Γ}
  : equiv F F' → equiv (F |₁ A) (F' |₁ A)
| ξ_parallel₂
    {Γ} {b y} {F F' : concretion ℍ ω Γ b y} {A : species ℍ ω Γ}
  : equiv F F' → equiv (A |₂ F) (A |₂ F')
| ξ_restriction
    {Γ} {b y} (M : affinity ℍ) {F F' : concretion ℍ ω (context.extend M.arity Γ) b y}
  : equiv F F' → equiv (ν'(M) F) (ν'(M) F')

-- Parallel is a commutative monoid
| parallel_nil
    {Γ} {b y} {F : concretion ℍ ω Γ b y}
  : equiv (F |₁ species.nil) F
| parallel_symm
    {Γ} {b y} {F : concretion ℍ ω Γ b y} {A : species ℍ ω Γ}
  : equiv (F |₁ A) (A |₂ F)
| parallel_assoc₁
    {Γ} {b y} {F : concretion ℍ ω Γ b y} {A B : species ℍ ω Γ}
  : equiv ((F |₁ A) |₁ B) (F |₁ (A |ₛ B))
| parallel_assoc₂
    {Γ} {b y} {F : concretion ℍ ω Γ b y} {A B : species ℍ ω Γ}
  : equiv ((A |₂ F) |₁ B) (A |₂ (F |₁ B))

-- Projections for species into parallel/apply
| ξ_parallel
    {Γ} {b y} {F : concretion ℍ ω Γ b y} {A B : species ℍ ω Γ}
  : A ≈ B → equiv (F |₁ A) (F |₁ B)
| ξ_apply
    {Γ} {b y} {bs : vector (name Γ) b} {A B : species ℍ ω (context.extend y Γ)}
  : A ≈ B → equiv (#(bs; y) A) (#(bs; y) B)

-- Standard ν rules
| ν_parallel₁
    {Γ} {b y} (M : affinity ℍ)
    {A : species ℍ ω Γ} {F : concretion ℍ ω (context.extend M.arity Γ) b y}
  : equiv (ν'(M)(species.rename name.extend A |₂ F)) (A |₂ ν'(M) F)
| ν_parallel₂
    {Γ} {b y} (M : affinity ℍ)
    {A : species ℍ ω (context.extend M.arity Γ)} {F : concretion ℍ ω Γ b y}
  : equiv (ν'(M)(concretion.rename name.extend F |₁ A)) (F |₁ (ν(M) A))
| ν_drop
    {Γ} {b y} (M : affinity ℍ) {F : concretion ℍ ω Γ b y}
  : equiv (ν'(M) rename name.extend F) F
| ν_swap
    {Γ} {b y} (M N : affinity ℍ)
    {F : concretion ℍ ω (context.extend N.arity (context.extend M.arity Γ)) b y}
  : equiv (ν'(M)ν'(N) F) (ν'(N)ν'(M) rename name.swap F)

| apply_parallel
    {Γ} {b y} {bs : vector (name Γ) b}
    {A : species ℍ ω Γ} {B : species ℍ ω (context.extend y Γ)}
  : equiv (#(bs; y) (species.rename name.extend A |ₛ B)) (A |₂ #(bs; y) B)

instance {Γ} {b y} : is_equiv (concretion ℍ ω Γ b y) equiv :=
  { refl := @equiv.refl ℍ _ _ Γ b y, symm := @equiv.symm ℍ _ _ Γ b y, trans := @equiv.trans ℍ _ _ Γ b y }
instance {Γ} {b y} : is_refl (concretion ℍ ω Γ b y) equiv := ⟨ λ _, equiv.refl ⟩

namespace equiv
  /-- The setoid of species under structural congruence. Can be brought into
      scope with the "congruence" locale. -/
  def setoid {Γ} {b y} : setoid (concretion ℍ ω Γ b y) :=
    ⟨ equiv, ⟨ @refl ℍ _ _ Γ b y, @symm ℍ _ _ Γ b y, @trans ℍ _ _ Γ b y ⟩ ⟩

  localized "attribute [instance] cpi.concretion.equiv.setoid" in congruence

  protected lemma ξ_parallel'
      {Γ} {b y} {F : concretion ℍ ω Γ b y} {A A' : species ℍ ω Γ} (eq : A ≈ A')
    : (A |₂ F) ≈ (A' |₂ F) :=
      calc  (A |₂ F)
          ≈ (F |₁ A) : symm parallel_symm
      ... ≈ (F |₁ A') : ξ_parallel eq
      ... ≈ (A' |₂ F) : parallel_symm

  protected lemma parallel_assoc₃
      {Γ} {b y : ℕ} {A B : species ℍ ω Γ} {F : concretion ℍ ω Γ b y}
    : ((A |ₛ B) |₂ F) ≈ (A |₂ B |₂ F) :=
    calc  ((A |ₛ B) |₂ F)
        ≈ (F |₁ (A |ₛ B)) : symm parallel_symm
    ... ≈ ((F |₁ A) |₁ B) : symm parallel_assoc₁
    ... ≈ ((A |₂ F) |₁ B) : ξ_parallel₁ parallel_symm
    ... ≈ (A |₂ F |₁ B) : parallel_assoc₂
    ... ≈ (A |₂ B |₂ F) : ξ_parallel₂ parallel_symm

end equiv
end concretion

end cpi

#lint-
