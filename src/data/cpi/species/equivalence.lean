import data.cpi.species.basic
import tactic.known_induct

set_option profiler true
set_option profiler.threshold 0.5

namespace cpi
namespace species

variable {ω : context}

/-- A chain of rewrite rule, to transform a species from one kind to another
    equivalent one. -/
inductive equiv : ∀ {Γ} (A B : species ω Γ), Prop
| refl  {Γ} {A : species ω Γ} : equiv A A
| trans {Γ} {A B C : species ω Γ} : equiv A B → equiv B C → equiv A C

-- Protections into the body of a species.
| ξ_parallel₁
      {Γ} {A A' B : species ω Γ}
    : equiv A A' → equiv (A |ₛ B) (A' |ₛ B)
| ξ_parallel₂
      {Γ} {A B B' : species ω Γ}
    : equiv B B' → equiv (A |ₛ B) (A |ₛ B')
| ξ_restriction
      {Γ} (M : affinity) {A A' : species ω (context.extend (M.arity) Γ)}
    : equiv A A' → equiv (ν(M) A) (ν(M) A')
| ξ_choice_here
      {Γ} {f} (π : prefix_expr Γ f) {A A' : species ω (f Γ)} {As : choices ω Γ}
    : equiv A A'
    → equiv (Σ# (whole.cons π A As)) (Σ# (whole.cons π A' As))
| ξ_choice_there
      {Γ} {f} (π : prefix_expr Γ f) {A : species ω (f Γ)} {As As' : choices ω Γ}
    : equiv (Σ# As) (Σ# As')
    → equiv (Σ# (whole.cons π A As)) (Σ# (whole.cons π A As'))

-- | An element in the choice array can be swapped.
| choice_swap
    {Γ} {f g} (π₁ : prefix_expr Γ f) (π₂ : prefix_expr Γ g)
    {A : species ω (f Γ)} {B : species ω (g Γ)} {As : choices ω Γ}
  : equiv (Σ# (whole.cons π₁ A (whole.cons π₂ B As)))
          (Σ# (whole.cons π₂ B (whole.cons π₁ A As)))

-- Species forms a commutative monoid using parallel.
| parallel_nil₁   : ∀ {Γ} {A : species ω Γ},     equiv (A |ₛ nil) A
| parallel_nil₂   : ∀ {Γ} {A : species ω Γ},     equiv A (A |ₛ nil)
| parallel_symm   : ∀ {Γ} {A B : species ω Γ},   equiv (A |ₛ B) (B |ₛ A)
| parallel_assoc₁ : ∀ {Γ} {A B C : species ω Γ}, equiv ((A |ₛ B) |ₛ C) (A |ₛ (B |ₛ C))
| parallel_assoc₂ : ∀ {Γ} {A B C : species ω Γ}, equiv (A |ₛ (B |ₛ C)) ((A |ₛ B) |ₛ C)

| ν_parallel₁
    {Γ} (M : affinity) {A : species ω Γ} {B : species ω (context.extend M.arity Γ)}
  : equiv (ν(M) (rename name.extend A |ₛ B)) (A |ₛ ν(M)B)
| ν_parallel₂
    {Γ} (M : affinity) {A : species ω Γ} {B : species ω (context.extend M.arity Γ)}
  : equiv (A |ₛ ν(M)B) (ν(M) (rename name.extend A |ₛ B))
| ν_drop₁
    {Γ} (M : affinity) {A : species ω Γ}
  : equiv (ν(M) (rename name.extend A)) A
| ν_drop₂
    {Γ} (M : affinity) {A : species ω Γ}
  : equiv A (ν(M) (rename name.extend A))
| ν_swap₁
    {Γ} (M N : affinity)
    {A  : species ω (context.extend N.arity (context.extend M.arity Γ))}
  : @equiv Γ (ν(M)ν(N) A) (ν(N)ν(M) rename name.swap A)
| ν_swap₂ -- Strictly the same as ν_swap₁, as name.swap is symmetric, but...
    {Γ} (M N : affinity)
    {A  : species ω (context.extend N.arity (context.extend M.arity Γ))}
  : @equiv Γ (ν(N)ν(M) rename name.swap A) (ν(M)ν(N) A)

namespace equiv
  protected lemma symm : ∀ {Γ} {A B : species ω Γ}, equiv A B → equiv B A
  | Γ A B eq := begin
    induction eq,
    case refl { from refl },
    case trans : Γ A B C ab bc ih_ab ih_bc { from trans ih_bc ih_ab },

    case ξ_parallel₁ : Γ A A' B eq ih { from ξ_parallel₁ ih },
    case ξ_parallel₂ : Γ A A' B eq ih { from ξ_parallel₂ ih },
    case ξ_restriction : Γ M A A' eq ih { from ξ_restriction M ih },
    case ξ_choice_here : Γ f π A A' As eq ih { from ξ_choice_here π ih },
    case ξ_choice_there : Γ f π A A' As eq ih { from ξ_choice_there π ih },

    case choice_swap { from choice_swap _ _ },

    case parallel_nil₁ { from parallel_nil₂ },
    case parallel_nil₂ { from parallel_nil₁ },
    case parallel_symm { from parallel_symm },
    case parallel_assoc₁ { from parallel_assoc₂ },
    case parallel_assoc₂ { from parallel_assoc₁ },

    case ν_parallel₁ : Γ M { from ν_parallel₂ M },
    case ν_parallel₂ : Γ M { from ν_parallel₁ M },
    case ν_drop₁ : Γ M { from ν_drop₂ M },
    case ν_drop₂ : Γ M { from ν_drop₁ M },
    case ν_swap₁ : Γ M N { from ν_swap₂ M N },
    case ν_swap₂ : Γ M N { from ν_swap₁ M N },
  end

end equiv

instance {Γ} : is_equiv (species ω Γ) equiv :=
  { refl := @equiv.refl _ Γ, symm := @equiv.symm _ Γ, trans := @equiv.trans _ Γ }
instance {Γ} : is_refl (species ω Γ) equiv := ⟨ λ _, equiv.refl ⟩
instance {Γ} : setoid (species ω Γ) :=
  ⟨ equiv, ⟨ @equiv.refl _ Γ, @equiv.symm _ Γ, @equiv.trans _ Γ ⟩ ⟩

-- -- Somewhat odd instance, but required for transitivity of the operator form.
instance setoid.is_equiv {Γ} : is_equiv (species ω Γ) has_equiv.equiv :=
  species.is_equiv

namespace equiv
  private lemma rename_swap
    {Γ Δ} {ρ : name Γ → name Δ} {M N : affinity}
    (A' : species ω (context.extend M.arity (context.extend N.arity Γ)))
    : rename (name.ext (name.ext ρ)) (rename name.swap A')
    = rename name.swap (rename (name.ext (name.ext ρ)) A')
    := by rw [rename_compose, name.swap_ext_ext, rename_compose]

  protected lemma rename :
      ∀ {Γ Δ} {A B : species ω Γ} (ρ : name Γ → name Δ)
      , A ≈ B → rename ρ A ≈ rename ρ B
    := begin
      intros _Γ _Δ _A _B _ρ _eq,
      known_induction species.equiv @equiv.rec_on ω
        (λ Γ A B, Π {Δ} (ρ : name Γ → name Δ), rename ρ A ≈ rename ρ B)
        _Γ _A _B _eq,

      case refl : Γ A Δ ρ { from refl },
      case trans : Γ A B C ab bc ih_ab ih_bc Δ ρ { from trans (ih_ab ρ) (ih_bc ρ) },

      -- Projection
      case ξ_parallel₁ : Γ A A' B eq ih Δ ρ { simp, from ξ_parallel₁ (ih ρ) },
      case ξ_parallel₂ : Γ A A' B eq ih Δ ρ { simp, from ξ_parallel₂ (ih ρ) },
      case ξ_restriction : Γ M A A' eq ih Δ ρ {
        simp,
        from ξ_restriction M (ih (name.ext ρ))
      },
      case ξ_choice_here : Γ f π A A' As eq ih Δ ρ {
        simp,
        from ξ_choice_here (prefix_expr.rename ρ π) (ih (prefix_expr.ext π ρ))
      },
      case ξ_choice_there : Γ f π A As As' eq ih Δ ρ {
        simp,
        have h := ih ρ,
        have g : (Σ# rename ρ As) ≈ (Σ# rename ρ As'), simp at h, from h,
        from ξ_choice_there (prefix_expr.rename ρ π) g
      },

      -- Choice
      case choice_swap : Γ f g π₁ π₂ A B As Δ ρ { simp, from choice_swap _ _ },

      -- Parallel
      case parallel_nil₁ : Γ A Δ ρ { simp, from parallel_nil₁ },
      case parallel_nil₂ : Γ A Δ ρ { simp, from parallel_nil₂ },
      case parallel_symm : Γ A B Δ ρ { simp, from parallel_symm },
      case parallel_assoc₁ : Γ A B C Δ ρ { simp, from parallel_assoc₁ },
      case parallel_assoc₂ : Γ A B C Δ ρ { simp, from parallel_assoc₂ },

      -- Restriction
      case ν_parallel₁ : Γ M A B Δ ρ {
        simp, rw ← species.rename_ext _, from ν_parallel₁ M
      },
      case ν_parallel₂ : Γ M A B Δ ρ {
        simp, rw ← species.rename_ext _, from ν_parallel₂ M
      },
      case ν_drop₁ : Γ M A Δ ρ {
        simp, rw ← species.rename_ext _, from ν_drop₁ M
      },
      case ν_drop₂ : Γ M A Δ ρ {
        simp, rw ← species.rename_ext _, from ν_drop₂ M
      },
      case ν_swap₁ : Γ M N A Δ ρ { simp, rw rename_swap _, from ν_swap₁ M N },
      case ν_swap₂ : Γ M N A Δ ρ { simp, rw rename_swap _, from ν_swap₂ M N },
    end

    lemma parallel_symm₁ {Γ} {A B C : species ω Γ} : (A |ₛ B |ₛ C) ≈ (B |ₛ A |ₛ C) :=
      calc  (A |ₛ (B |ₛ C))
          ≈ ((A |ₛ B) |ₛ C) : parallel_assoc₂
      ... ≈ ((B |ₛ A) |ₛ C) : ξ_parallel₁ parallel_symm
      ... ≈ (B |ₛ (A |ₛ C)) : parallel_assoc₁

    lemma parallel_symm₂ {Γ} {A B C : species ω Γ} : ((A |ₛ B) |ₛ C) ≈ ((A |ₛ C) |ₛ B) :=
      calc  ((A |ₛ B) |ₛ C)
          ≈ (A |ₛ (B |ₛ C)) : parallel_assoc₁
      ... ≈ (A |ₛ (C |ₛ B)) : ξ_parallel₂ parallel_symm
      ... ≈ ((A |ₛ C) |ₛ B) : parallel_assoc₂

    lemma ν_parallel' {Γ} (M : affinity) {A : species ω (context.extend M.arity Γ)} {B : species ω Γ}
      : (ν(M) (A |ₛ rename name.extend B)) ≈ ((ν(M)A) |ₛ B) :=
      calc  (ν(M) A |ₛ rename name.extend B)
          ≈ (ν(M) rename name.extend B |ₛ A) : ξ_restriction M parallel_symm
      ... ≈ (B |ₛ ν(M) A) : ν_parallel₁ M
      ... ≈ ((ν(M) A) |ₛ B) : parallel_symm

    lemma parallel_nil' {Γ} {A : species ω Γ} : (nil |ₛ A) ≈ A :=
      calc  (nil |ₛ A)
          ≈ (A |ₛ nil) : parallel_symm
      ... ≈ A : parallel_nil₁
end equiv

namespace parallel
  lemma from_list_cons {Γ} (A : species ω Γ) :
    ∀ (Bs : list(species ω Γ)), from_list (A :: Bs) ≈ (A |ₛ from_list Bs)
  | [] := equiv.parallel_nil₂
  | (B :: Bs) := refl _

  lemma from_to_append {Γ} :
    ∀ (As : list (species ω Γ)) (B : species ω Γ)
    , from_list (As ++ to_list B) ≈ (from_list As |ₛ from_list (to_list B))
  | [] B := by { simp only [list.nil_append], from symm equiv.parallel_nil' }
  | [A] B := from_list_cons A _
  | (A :: A' :: As) B := begin
      have h := from_to_append (A' :: As) B,
      simp only [from_list, list.cons_append],
      from calc  (A |ₛ from_list (A' :: (As ++ to_list B)))
               ≈ (A |ₛ (from_list (A' :: As) |ₛ from_list (to_list B)))
                 : equiv.ξ_parallel₂ h
           ... ≈ ((A |ₛ from_list (A' :: As)) |ₛ from_list (to_list B))
                : symm equiv.parallel_assoc₁
    end

  lemma from_to {Γ} : ∀ (A : species ω Γ), from_list (to_list A) ≈ A
  | nil := by unfold from_list to_list
  | (Σ# _) := by unfold from_list to_list
  | (ν(_) _) := by unfold from_list to_list
  | (apply _ _) := by unfold from_list to_list
  | (A |ₛ B) := begin
      unfold from_list to_list,
      have a := from_to A, have b := from_to B,
      from calc  from_list (to_list A ++ to_list B)
               ≈ (from_list (to_list A) |ₛ from_list (to_list B))
                 : from_to_append (to_list A) B
           ... ≈ (from_list (to_list A) |ₛ B) : equiv.ξ_parallel₂ b
           ... ≈ (A |ₛ B) : equiv.ξ_parallel₁ a,
    end

  lemma from_to_append₂ {Γ} (A B : species ω Γ)
    : from_list (to_list A ++ to_list B) ≈ (A |ₛ B) := begin
    have h : to_list A ++ to_list B = to_list (A |ₛ B), unfold to_list,
    rw h, from from_to _,
  end

  private lemma from_cons {Γ} :
    ∀ (A : species ω Γ) {As Bs : list _}
    , from_list As ≈ from_list Bs
    → from_list (A :: As) ≈ from_list (A :: Bs)
  | A [] [] _ := refl _
  | A [] (B' :: Bs) eq :=
      calc  A
          ≈ (A |ₛ nil) : equiv.parallel_nil₂
      ... ≈ (A |ₛ from_list (B' :: Bs)) : equiv.ξ_parallel₂ eq
  | A (A' :: As) [] eq :=
      calc  (A |ₛ from_list (A' :: As))
          ≈ (A |ₛ nil) : equiv.ξ_parallel₂ eq
      ... ≈ A : equiv.parallel_nil₁
  | A (A' :: As) (B' :: Bs') eq := equiv.ξ_parallel₂ eq

  lemma permute {Γ} :
    ∀ {As Bs : list (species ω Γ)}
    , As ≈ Bs → from_list As ≈ from_list Bs := λ _ _ perm, begin
    induction perm,

    case list.perm.nil { from refl _ },
    case list.perm.skip : A As Bs pm ih { from from_cons A ih },
    case list.perm.swap : A B As {
      cases As,
      case list.nil { from equiv.parallel_symm },
      case list.cons { from equiv.parallel_symm₁ },
    },
    case list.perm.trans : As Bs Cs ab bc ih_ab ih_bc { from trans ih_ab ih_bc }
  end
end parallel

namespace choice
  lemma permute {Γ} :
    ∀ {As Bs : list (Σ' {f} (π : prefix_expr Γ f), species ω (f Γ))}
    , As ≈ Bs → (Σ# from_list As) ≈ (Σ# from_list Bs) := λ _ _ perm, begin
    induction perm,

    case list.perm.nil { from refl _ },
    case list.perm.skip : A As Bs pm ih {
      cases A with f this, cases this with π A,
      unfold from_list,
      from equiv.ξ_choice_there π ih
     },
    case list.perm.swap : A B As {
      rcases A with ⟨ f₁, π₁, A ⟩, rcases B with ⟨ f₂, π₂, B ⟩,
      from equiv.choice_swap π₂ π₁
    },
    case list.perm.trans : As Bs Cs ab bc ih_ab ih_bc { from trans ih_ab ih_bc }
  end
end choice

section examples
  variable {Γ : context}
  variables A A' B C : species ω Γ

  example : A ≈ (A |ₛ nil) := symm equiv.parallel_nil₁

  example : A ≈ (nil |ₛ A) := trans equiv.parallel_nil₂ equiv.parallel_symm

  example : A ≈ A' → (A |ₛ B) ≈ C → (A' |ₛ B) ≈ C := begin
    assume a eq,
    from trans (symm $ equiv.ξ_parallel₁ a) eq
  end
end examples

end species
end cpi

#lint
