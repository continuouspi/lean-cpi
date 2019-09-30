import data.cpi.species.basic
import tactic.known_induct

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi
namespace species

variable {ω : environment}

/-- A chain of rewrite rule, to transform a species from one kind to another
    equivalent one. -/
inductive equiv : ∀ {Γ : context ω} (A B : species Γ), Prop
| refl  {Γ} {A : species Γ} : equiv A A
| trans {Γ} {A B C : species Γ} : equiv A B → equiv B C → equiv A C
| symm  {Γ} {A B : species Γ} : equiv A B → equiv B A

-- Protections into the body of a species.
| ξ_parallel₁
      {Γ} {A A' B : species Γ}
    : equiv A A' → equiv (A |ₛ B) (A' |ₛ B)
| ξ_parallel₂
      {Γ} {A B B' : species Γ}
    : equiv B B' → equiv (A |ₛ B) (A |ₛ B')
| ξ_restriction
      {Γ} (M : affinity) {A A' : species (context.extend (M.arity) Γ)}
    : equiv A A' → equiv (ν(M) A) (ν(M) A')
| ξ_choice_cons
      {Γ} {f} (π : prefix_expr Γ f) {A A' : species (f Γ)} {As : choices Γ}
    : equiv A A'
    → equiv (Σ# (whole.cons π A As)) (Σ# (whole.cons π A' As))

-- | An element in the choice array can be swapped.
| choice_swap
    {Γ} {f g} (π₁ : prefix_expr Γ f) (π₂ : prefix_expr Γ g)
    {A : species (f Γ)} {B : species (g Γ)} {As : choices Γ}
  : equiv (Σ# (whole.cons π₁ A (whole.cons π₂ B As)))
          (Σ# (whole.cons π₂ B (whole.cons π₁ A As)))

-- Species forms a commutative monoid using parallel.
| parallel_nil   : ∀ {Γ} {A : species Γ},     equiv (A |ₛ nil) A
| parallel_symm  : ∀ {Γ} {A B : species Γ},   equiv (A |ₛ B) (B |ₛ A)
| parallel_assoc : ∀ {Γ} {A B C : species Γ}, equiv ((A |ₛ B) |ₛ C) (A |ₛ (B |ₛ C))

| ν_parallel
    {Γ} (M : affinity) {A : species Γ} {B : species (context.extend M.arity Γ)}
  : equiv (ν(M) (rename name.extend A |ₛ B)) (A |ₛ ν(M)B)
| ν_drop
    {Γ} (M : affinity) {A : species Γ}
  : equiv (ν(M) (rename name.extend A)) A
| ν_swap
    {Γ} (M N : affinity)
    {A  : species (context.extend N.arity (context.extend M.arity Γ))}
  : @equiv Γ (ν(M)ν(N) A) (ν(N)ν(M) rename name.swap A)

instance {Γ : context ω} : is_equiv (species Γ) equiv :=
  { refl := @equiv.refl _ Γ, symm := @equiv.symm _ Γ, trans := @equiv.trans _ Γ }
instance {Γ : context ω} : is_refl (species Γ) equiv := ⟨ λ _, equiv.refl ⟩
instance {Γ : context ω} : setoid (species Γ) :=
  ⟨ equiv, ⟨ @equiv.refl _ Γ, @equiv.symm _ Γ, @equiv.trans _ Γ ⟩ ⟩

-- -- Somewhat odd instance, but required for transitivity of the operator form.
instance setoid.is_equiv {Γ : context ω} : is_equiv (species Γ) has_equiv.equiv :=
  species.is_equiv

namespace equiv
  private lemma rename_swap
    {Γ Δ : context ω} {ρ : name Γ → name Δ} {M N : affinity}
    (A' : species (context.extend M.arity (context.extend N.arity Γ)))
    : rename (name.ext (name.ext ρ)) (rename name.swap A')
    = rename name.swap (rename (name.ext (name.ext ρ)) A')
    := by rw [rename_compose, name.swap_ext_ext, rename_compose]

  protected lemma rename :
      ∀ {Γ Δ : context ω} {A B : species Γ} (ρ : name Γ → name Δ)
      , A ≈ B → rename ρ A ≈ rename ρ B
    := begin
      intros _Γ _Δ _A _B _ρ _eq,
      known_induction species.equiv @equiv.rec_on ω
        (λ Γ A B, Π {Δ} (ρ : name Γ → name Δ), rename ρ A ≈ rename ρ B)
        _Γ _A _B _eq,

      case refl : Γ A Δ ρ { from refl },
      case trans : Γ A B C ab bc ih_ab ih_bc Δ ρ { from trans (ih_ab ρ) (ih_bc ρ) },
      case symm : Γ A B eq ih Δ ρ { from symm (ih ρ) },

      -- Projection
      case ξ_parallel₁ : Γ A A' B eq ih Δ ρ { simp, from ξ_parallel₁ (ih ρ) },
      case ξ_parallel₂ : Γ A A' B eq ih Δ ρ { simp, from ξ_parallel₂ (ih ρ) },
      case ξ_restriction : Γ M A A' eq ih Δ ρ {
        simp,
        from ξ_restriction M (ih (name.ext ρ))
      },
      case ξ_choice_cons : Γ f π A A' As eq ih Δ ρ {
        simp,
        from ξ_choice_cons (prefix_expr.rename ρ π) (ih (prefix_expr.ext π ρ))
      },

      -- Choice
      case choice_swap : Γ f g π₁ π₂ A B As Δ ρ { simp, from choice_swap _ _ },

      -- Parallel
      case parallel_nil : Γ A Δ ρ { simp, from parallel_nil },
      case parallel_symm : Γ A B Δ ρ { simp, from parallel_symm },
      case parallel_assoc : Γ A B C Δ ρ { simp, from parallel_assoc },

      -- Restriction
      case ν_parallel : Γ M A B Δ ρ {
        simp, rw ← species.rename_ext _, from ν_parallel M
      },
      case ν_drop : Γ M A Δ ρ {
        simp, rw ← species.rename_ext _, from ν_drop M
      },
      case ν_swap : Γ M N A Δ ρ {
        simp, rw rename_swap _, from ν_swap M N
      }
    end

    lemma parallel_symm₁ {Γ : context ω} {A B C : species Γ} : (A |ₛ B |ₛ C) ≈ (B |ₛ A |ₛ C) :=
      calc  (A |ₛ (B |ₛ C))
          ≈ ((A |ₛ B) |ₛ C) : symm (@parallel_assoc _ _ A B C)
      ... ≈ ((B |ₛ A) |ₛ C) : ξ_parallel₁ parallel_symm
      ... ≈ (B |ₛ (A |ₛ C)) : parallel_assoc

    lemma parallel_symm₂ {Γ : context ω} {A B C : species Γ} : ((A |ₛ B) |ₛ C) ≈ ((A |ₛ C) |ₛ B) :=
      calc  ((A |ₛ B) |ₛ C)
          ≈ (A |ₛ (B |ₛ C)) : parallel_assoc
      ... ≈ (A |ₛ (C |ₛ B)) : ξ_parallel₂ parallel_symm
      ... ≈ ((A |ₛ C) |ₛ B) : symm parallel_assoc

    lemma ν_parallel' {Γ : context ω} (M : affinity) {A : species (context.extend M.arity Γ)} {B : species Γ}
      : (ν(M) (A |ₛ rename name.extend B)) ≈ ((ν(M)A) |ₛ B) :=
      calc  (ν(M) A |ₛ rename name.extend B)
          ≈ (ν(M) rename name.extend B |ₛ A) : ξ_restriction M parallel_symm
      ... ≈ (B |ₛ ν(M) A) : ν_parallel M
      ... ≈ ((ν(M) A) |ₛ B) : parallel_symm
end equiv

section examples
  variable Γ : context ω
  variables A A' B C : species Γ

  example : A ≈ (A |ₛ nil) := symm equiv.parallel_nil

  example : A ≈ (nil |ₛ A) :=
    trans
      (symm equiv.parallel_nil)
      equiv.parallel_symm

  example : A ≈ A' → (A |ₛ B) ≈ C → (A' |ₛ B) ≈ C := begin
    assume a eq,
    from trans (symm $ equiv.ξ_parallel₁ a) eq
  end
end examples

end species
end cpi

#sanity_check
