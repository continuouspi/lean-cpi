import data.cpi.species.basic

namespace cpi
namespace species

variables {ℍ : Type} {ω : context}

/-- A chain of rewrite rules, to transform a species from one kind to another
    equivalent one. -/
inductive equivalent : ∀ {Γ} (A B : species ℍ ω Γ), Type
| refl  {Γ} {A : species ℍ ω Γ} : equivalent A A
| trans {Γ} {A B C : species ℍ ω Γ} : equivalent A B → equivalent B C → equivalent A C

-- Protections into the body of a species.
| ξ_parallel₁
      {Γ} {A A' B : species ℍ ω Γ}
    : equivalent A A' → equivalent (A |ₛ B) (A' |ₛ B)
| ξ_parallel₂
      {Γ} {A B B' : species ℍ ω Γ}
    : equivalent B B' → equivalent (A |ₛ B) (A |ₛ B')
| ξ_restriction
      {Γ} (M : affinity ℍ) {A A' : species ℍ ω (context.extend (M.arity) Γ)}
    : equivalent A A' → equivalent (ν(M) A) (ν(M) A')
| ξ_choice_here
      {Γ} {f} (π : prefix_expr ℍ Γ f) {A A' : species ℍ ω (f.apply Γ)} {As : choices ℍ ω Γ}
    : equivalent A A'
    → equivalent (Σ# (whole.cons π A As)) (Σ# (whole.cons π A' As))
| ξ_choice_there
      {Γ} {f} (π : prefix_expr ℍ Γ f) {A : species ℍ ω (f.apply Γ)} {As As' : choices ℍ ω Γ}
    : equivalent (Σ# As) (Σ# As')
    → equivalent (Σ# (whole.cons π A As)) (Σ# (whole.cons π A As'))

-- | An element in the choice array can be swapped.
| choice_swap
    {Γ} {f g} (π₁ : prefix_expr ℍ Γ f) (π₂ : prefix_expr ℍ Γ g)
    {A : species ℍ ω (f.apply Γ)} {B : species ℍ ω (g.apply Γ)} {As : choices ℍ ω Γ}
  : equivalent (Σ# (whole.cons π₁ A (whole.cons π₂ B As)))
          (Σ# (whole.cons π₂ B (whole.cons π₁ A As)))

-- Species forms a commutative monoid using parallel.
| parallel_nil₁   {Γ} {A : species ℍ ω Γ}     : equivalent (A |ₛ nil) A
| parallel_nil₂   {Γ} {A : species ℍ ω Γ}     : equivalent A (A |ₛ nil)
| parallel_symm   {Γ} {A B : species ℍ ω Γ}   : equivalent (A |ₛ B) (B |ₛ A)
| parallel_assoc₁ {Γ} {A B C : species ℍ ω Γ} : equivalent ((A |ₛ B) |ₛ C) (A |ₛ (B |ₛ C))
| parallel_assoc₂ {Γ} {A B C : species ℍ ω Γ} : equivalent (A |ₛ (B |ₛ C)) ((A |ₛ B) |ₛ C)

| ν_parallel₁
    {Γ} (M : affinity ℍ) {A : species ℍ ω Γ} {B : species ℍ ω (context.extend M.arity Γ)}
  : equivalent (ν(M) (rename name.extend A |ₛ B)) (A |ₛ ν(M)B)
| ν_parallel₂
    {Γ} (M : affinity ℍ) {A : species ℍ ω Γ} {B : species ℍ ω (context.extend M.arity Γ)}
  : equivalent (A |ₛ ν(M)B) (ν(M) (rename name.extend A |ₛ B))
| ν_drop₁
    {Γ} (M : affinity ℍ) {A : species ℍ ω Γ}
  : equivalent (ν(M) (rename name.extend A)) A
| ν_drop₂
    {Γ} (M : affinity ℍ) {A : species ℍ ω Γ}
  : equivalent A (ν(M) (rename name.extend A))
| ν_swap₁
    {Γ} (M N : affinity ℍ)
    {A  : species ℍ ω (context.extend N.arity (context.extend M.arity Γ))}
  : equivalent (ν(M)ν(N) A) (ν(N)ν(M) rename name.swap A)
| ν_swap₂ -- Strictly the same as ν_swap₁, as name.swap is symmetric, but...
    {Γ} (M N : affinity ℍ)
    {A  : species ℍ ω (context.extend N.arity (context.extend M.arity Γ))}
  : @equivalent Γ (ν(N)ν(M) rename name.swap A) (ν(M)ν(N) A)

namespace equivalent
  /-- Flip an equivalence relationship. -/
  protected def symm : ∀ {Γ} {A B : species ℍ ω Γ}, equivalent A B → equivalent B A
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

  /-- Flipping an equivalence relation twice gives the original. -/
  protected lemma symm_symm :
    ∀ {Γ} {A B : species ℍ ω Γ} (eq : equivalent A B)
    , eq = equivalent.symm (equivalent.symm eq)
  | Γ A B eq := begin
    induction eq,
    case equivalent.refl { from rfl },
    case equivalent.trans : Γ A B C ab bc ih_ab ih_bc {
      from congr_arg2 trans ih_ab ih_bc,
    },
    case ξ_parallel₁ : Γ A A' B eq ih { from congr_arg ξ_parallel₁ ih, },
    case ξ_parallel₂ : Γ A A' B eq ih { from congr_arg ξ_parallel₂ ih },
    case ξ_restriction : Γ M A A' eq ih { from congr_arg (ξ_restriction M) ih },
    case ξ_choice_here : Γ f π A A' As eq ih { from congr_arg (ξ_choice_here π) ih },
    case ξ_choice_there : Γ f π A A' As eq ih { from congr_arg (ξ_choice_there π) ih },

    repeat { from rfl },
  end

  local infix ` ~ ` := equivalent

  private def rename_swap
    {Γ Δ} {ρ : name Γ → name Δ} {M N : affinity ℍ}
    (A' : species ℍ ω (context.extend M.arity (context.extend N.arity Γ)))
    : rename (name.ext (name.ext ρ)) (rename name.swap A')
    = rename name.swap (rename (name.ext (name.ext ρ)) A')
    := by rw [rename_compose, name.swap_ext_ext, rename_compose]

  /-- Rename an equivalence relationship. -/
  protected def rename :
      ∀ {Γ Δ} {A B : species ℍ ω Γ} (ρ : name Γ → name Δ)
      , A ~ B → rename ρ A ~ rename ρ B
    | Γ Δ A B ρ eq := begin
      induction eq generalizing Δ,

      case refl : Γ A Δ ρ { from refl },
      case trans : Γ A B C ab bc ih_ab ih_bc { from trans (ih_ab _ ρ) (ih_bc _ ρ) },

      -- Projection
      case ξ_parallel₁ : Γ A A' B eq ih { simp, from ξ_parallel₁ (ih _ ρ) },
      case ξ_parallel₂ : Γ A A' B eq ih { simp, from ξ_parallel₂ (ih _ ρ) },
      case ξ_restriction : Γ M A A' eq ih {
        simp,
        from ξ_restriction M (ih _ (name.ext ρ))
      },
      case ξ_choice_here : Γ f π A A' As eq ih {
        simp,
        from ξ_choice_here (prefix_expr.rename ρ π) (ih _ (prefix_expr.ext π ρ))
      },
      case ξ_choice_there : Γ f π A As As' eq ih {
        simp,
        have h := ih _ ρ,
        have g : (Σ# species.rename ρ As) ~ (Σ# species.rename ρ As'), simp at h, from h,
        from ξ_choice_there (prefix_expr.rename ρ π) g
      },

      -- Choice
      case choice_swap : Γ f g π₁ π₂ A B As { simp, from choice_swap _ _ },

      -- Parallel
      case parallel_nil₁ : Γ A { simp, from parallel_nil₁ },
      case parallel_nil₂ : Γ A { simp, from parallel_nil₂ },
      case parallel_symm : Γ A B { simp, from parallel_symm },
      case parallel_assoc₁ : Γ A B C { simp, from parallel_assoc₁ },
      case parallel_assoc₂ : Γ A B C { simp, from parallel_assoc₂ },

      -- Restriction
      case ν_parallel₁ : Γ M A B {
        simp, rw ← species.rename_ext _, from ν_parallel₁ M
      },
      case ν_parallel₂ : Γ M A B {
        simp, rw ← species.rename_ext _, from ν_parallel₂ M
      },
      case ν_drop₁ : Γ M A {
        simp, rw ← species.rename_ext _, from ν_drop₁ M
      },
      case ν_drop₂ : Γ M A {
        simp, rw ← species.rename_ext _, from ν_drop₂ M
      },
      case ν_swap₁ : Γ M N A { simp, rw rename_swap _, from ν_swap₁ M N },
      case ν_swap₂ : Γ M N A { simp, rw rename_swap _, from ν_swap₂ M N },
    end
end equivalent

/-- Lower an equivalence relationship to a proof-irrelevant proposition.

    This allows us to use it as a normal proof object, while -/
inductive equiv {Γ} (A B : species ℍ ω Γ) : Prop
| intro : equivalent A B → equiv

namespace equiv
  local infix ` ~ ` := equiv
  @[pattern]
  protected lemma refl {Γ} (A : species ℍ ω Γ) : A ~ A := ⟨ equivalent.refl ⟩

  @[pattern]
  protected lemma rfl {Γ} {A : species ℍ ω Γ} : A ~ A := equiv.refl A

  protected lemma symm {Γ} {A B : species ℍ ω Γ} : A ~ B → B ~ A
  | ⟨ eq ⟩ := ⟨ equivalent.symm eq ⟩

  @[pattern]
  protected lemma trans {Γ} {A B C : species ℍ ω Γ} : A ~ B → B ~ C → A ~ C
  | ⟨ ab ⟩ ⟨ bc ⟩ := ⟨ equivalent.trans ab bc ⟩

  protected lemma rename {Γ Δ} {A B : species ℍ ω Γ} (ρ : name Γ → name Δ)
    : A ~ B → rename ρ A ~ rename ρ B
  | ⟨ eq ⟩ := ⟨ equivalent.rename ρ eq ⟩

  @[pattern]
  lemma ξ_parallel₁ {Γ} {A A' B : species ℍ ω Γ} : A ~ A' → (A |ₛ B) ~ (A' |ₛ B)
  | ⟨ eq ⟩ := ⟨ equivalent.ξ_parallel₁ eq ⟩

  @[pattern]
  lemma ξ_parallel₂ {Γ} {A B B' : species ℍ ω Γ} : B ~ B' → (A |ₛ B) ~ (A |ₛ B')
  | ⟨ eq ⟩ := ⟨ equivalent.ξ_parallel₂ eq ⟩

  @[pattern]
  lemma ξ_restriction {Γ} (M : affinity ℍ) {A A' : species ℍ ω (context.extend (M.arity) Γ)}
    : A ~ A' → (ν(M) A) ~ (ν(M) A')
  | ⟨ eq ⟩ := ⟨ equivalent.ξ_restriction M eq ⟩

  @[pattern]
  lemma ξ_choice_here
      {Γ} {f} (π : prefix_expr ℍ Γ f) {A A' : species ℍ ω (f.apply Γ)} {As : choices ℍ ω Γ}
    : A ~ A' → (Σ# (whole.cons π A As)) ~ (Σ# (whole.cons π A' As))
  | ⟨ eq ⟩ := ⟨ equivalent.ξ_choice_here π eq ⟩

  @[pattern]
  lemma ξ_choice_there
      {Γ} {f} (π : prefix_expr ℍ Γ f) {A : species ℍ ω (f.apply Γ)} {As As' : choices ℍ ω Γ}
    : (Σ# As) ~ (Σ# As')
    → (Σ# (whole.cons π A As)) ~ (Σ# (whole.cons π A As'))
  | ⟨ eq ⟩ := ⟨ equivalent.ξ_choice_there π eq ⟩

  @[pattern]
  lemma choice_swap
      {Γ} {f g} (π₁ : prefix_expr ℍ Γ f) (π₂ : prefix_expr ℍ Γ g)
      {A : species ℍ ω (f.apply Γ)} {B : species ℍ ω (g.apply Γ)} {As : choices ℍ ω Γ}
    : (Σ# (whole.cons π₁ A (whole.cons π₂ B As))) ~ (Σ# (whole.cons π₂ B (whole.cons π₁ A As)))
    := ⟨ equivalent.choice_swap π₁ π₂ ⟩

  @[pattern]
  lemma parallel_nil₁   {Γ} {A : species ℍ ω Γ}     : (A |ₛ nil) ~ A := ⟨ equivalent.parallel_nil₁ ⟩

  @[pattern]
  lemma parallel_nil₂   {Γ} {A : species ℍ ω Γ}     : A ~ (A |ₛ nil) := ⟨ equivalent.parallel_nil₂ ⟩

  @[pattern]
  lemma parallel_symm   {Γ} {A B : species ℍ ω Γ}   : (A |ₛ B) ~ (B |ₛ A) := ⟨ equivalent.parallel_symm ⟩

  @[pattern]
  lemma parallel_assoc₁ {Γ} {A B C : species ℍ ω Γ} : ((A |ₛ B) |ₛ C) ~ (A |ₛ (B |ₛ C)) := ⟨ equivalent.parallel_assoc₁ ⟩

  @[pattern]
  lemma parallel_assoc₂ {Γ} {A B C : species ℍ ω Γ} : (A |ₛ (B |ₛ C)) ~ ((A |ₛ B) |ₛ C) := ⟨ equivalent.parallel_assoc₂ ⟩

  @[pattern]
  lemma ν_parallel₁
      {Γ} (M : affinity ℍ) {A : species ℍ ω Γ} {B : species ℍ ω (context.extend M.arity Γ)}
    : (ν(M) (rename name.extend A |ₛ B)) ~ (A |ₛ ν(M)B)
    := ⟨ equivalent.ν_parallel₁ M ⟩

  @[pattern]
  lemma ν_parallel₂
      {Γ} (M : affinity ℍ) {A : species ℍ ω Γ} {B : species ℍ ω (context.extend M.arity Γ)}
    : (A |ₛ ν(M)B) ~ (ν(M) (rename name.extend A |ₛ B))
    := ⟨ equivalent.ν_parallel₂ M ⟩

  @[pattern]
  lemma ν_drop₁ {Γ} (M : affinity ℍ) {A : species ℍ ω Γ} : (ν(M) (rename name.extend A)) ~ A
    := ⟨ equivalent.ν_drop₁ M ⟩

  @[pattern]
  lemma ν_drop₂ {Γ} (M : affinity ℍ) {A : species ℍ ω Γ} : A ~ (ν(M) (rename name.extend A))
    := ⟨ equivalent.ν_drop₂ M ⟩

  @[pattern]
  lemma ν_swap₁
      {Γ} (M N : affinity ℍ) {A : species ℍ ω (context.extend N.arity (context.extend M.arity Γ))}
    : (ν(M)ν(N) A) ~ (ν(N)ν(M) rename name.swap A)
    := ⟨ equivalent.ν_swap₁ M N ⟩

  @[pattern]
  lemma ν_swap₂ -- Strictly the same as ν_swap₁, as name.swap is symmetric, but...
      {Γ} (M N : affinity ℍ) {A : species ℍ ω (context.extend N.arity (context.extend M.arity Γ))}
    : (ν(N)ν(M) rename name.swap A) ~ (ν(M)ν(N) A)
    := ⟨ equivalent.ν_swap₂ M N ⟩
end equiv

instance {Γ} : is_equiv (species ℍ ω Γ) equiv :=
  { refl := equiv.refl, symm := @equiv.symm ℍ ω Γ, trans := @equiv.trans ℍ ω Γ }
instance {Γ} : is_refl (species ℍ ω Γ) equiv := ⟨ equiv.refl ⟩
instance {Γ} : setoid (species ℍ ω Γ) :=
  ⟨ equiv, ⟨ @equiv.refl ℍ ω Γ, @equiv.symm ℍ ω Γ, @equiv.trans ℍ ω Γ ⟩ ⟩

-- -- Somewhat odd instance, but required for transitivity of the operator form.
instance setoid.is_equiv {Γ} : is_equiv (species ℍ ω Γ) has_equiv.equiv :=
  species.is_equiv

namespace equiv
  lemma parallel_symm₁ {Γ} {A B C : species ℍ ω Γ} : (A |ₛ B |ₛ C) ≈ (B |ₛ A |ₛ C) :=
    calc  (A |ₛ (B |ₛ C))
        ≈ ((A |ₛ B) |ₛ C) : parallel_assoc₂
    ... ≈ ((B |ₛ A) |ₛ C) : ξ_parallel₁ parallel_symm
    ... ≈ (B |ₛ (A |ₛ C)) : parallel_assoc₁

  lemma parallel_symm₂ {Γ} {A B C : species ℍ ω Γ} : ((A |ₛ B) |ₛ C) ≈ ((A |ₛ C) |ₛ B) :=
    calc  ((A |ₛ B) |ₛ C)
        ≈ (A |ₛ (B |ₛ C)) : parallel_assoc₁
    ... ≈ (A |ₛ (C |ₛ B)) : ξ_parallel₂ parallel_symm
    ... ≈ ((A |ₛ C) |ₛ B) : parallel_assoc₂

  lemma ν_parallel' {Γ} (M : affinity ℍ) {A : species ℍ ω (context.extend M.arity Γ)} {B : species ℍ ω Γ}
    : (ν(M) (A |ₛ rename name.extend B)) ≈ ((ν(M)A) |ₛ B) :=
    calc  (ν(M) A |ₛ rename name.extend B)
        ≈ (ν(M) rename name.extend B |ₛ A) : ξ_restriction M parallel_symm
    ... ≈ (B |ₛ ν(M) A) : ν_parallel₁ M
    ... ≈ ((ν(M) A) |ₛ B) : parallel_symm

  lemma parallel_nil' {Γ} {A : species ℍ ω Γ} : (nil |ₛ A) ≈ A :=
    calc  (nil |ₛ A)
        ≈ (A |ₛ nil) : parallel_symm
    ... ≈ A : parallel_nil₁
end equiv

namespace parallel
  lemma from_list_cons {Γ} (A : species ℍ ω Γ) :
    ∀ (Bs : list(species ℍ ω Γ)), from_list (A :: Bs) ≈ (A |ₛ from_list Bs)
  | [] := equiv.parallel_nil₂
  | (B :: Bs) := refl _

  lemma from_append {Γ} :
    ∀ (As : list (species ℍ ω Γ)) (Bs : list (species ℍ ω Γ))
    , from_list (As ++ Bs) ≈ (from_list As |ₛ from_list Bs)
  | [] B := by { simp only [list.nil_append], from symm equiv.parallel_nil' }
  | [A] B := from_list_cons A _
  | (A :: A' :: As) B := begin
      have h := from_append (A' :: As) B,
      simp only [from_list, list.cons_append],
      from calc  (A |ₛ from_list (A' :: (As ++ B)))
               ≈ (A |ₛ (from_list (A' :: As) |ₛ from_list B))
                 : equiv.ξ_parallel₂ h
           ... ≈ ((A |ₛ from_list (A' :: As)) |ₛ from_list B)
                : symm equiv.parallel_assoc₁
    end

  lemma from_to {Γ} : ∀ (A : species ℍ ω Γ), from_list (to_list A) ≈ A
  | nil := by unfold from_list to_list
  | (Σ# _) := by unfold from_list to_list
  | (ν(_) _) := by unfold from_list to_list
  | (apply _ _) := by unfold from_list to_list
  | (A |ₛ B) := begin
      unfold from_list to_list,
      have a := from_to A, have b := from_to B,
      from calc  from_list (to_list A ++ to_list B)
               ≈ (from_list (to_list A) |ₛ from_list (to_list B))
                 : from_append (to_list A) (to_list B)
           ... ≈ (from_list (to_list A) |ₛ B) : equiv.ξ_parallel₂ b
           ... ≈ (A |ₛ B) : equiv.ξ_parallel₁ a,
    end

  lemma from_to_append {Γ} (A B : species ℍ ω Γ)
    : from_list (to_list A ++ to_list B) ≈ (A |ₛ B) := begin
    have h : to_list A ++ to_list B = to_list (A |ₛ B), unfold to_list,
    rw h, from from_to _,
  end

  private lemma from_cons {Γ} :
    ∀ (A : species ℍ ω Γ) {As Bs : list _}
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
    ∀ {As Bs : list (species ℍ ω Γ)}
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

  namespace quot
    /-- Make a parallel species from a quotient of two species. -/
    def mk {Γ} : quotient (@species.setoid ℍ ω Γ) → quotient (@species.setoid ℍ ω Γ) → quotient (@species.setoid ℍ ω Γ)
    | A B := quotient.lift_on₂ A B (λ A B, ⟦ A |ₛ B ⟧)
        (λ A B A' B' eqA eqB, quot.sound (trans (equiv.ξ_parallel₁ eqA) ((equiv.ξ_parallel₂ eqB))))

    lemma assoc {Γ} (A B C : quotient (@species.setoid ℍ ω Γ))
      : mk A (mk B C) = mk (mk A B) C
      := begin
        rcases quot.exists_rep A with ⟨ A, ⟨ _ ⟩ ⟩,
        rcases quot.exists_rep B with ⟨ B, ⟨ _ ⟩ ⟩,
        rcases quot.exists_rep C with ⟨ C, ⟨ _ ⟩ ⟩,
        from quot.sound equiv.parallel_assoc₂,
      end

    /-- parallel.from_list, lifted to the level of quotients. -/
    def from_list {Γ} :
      list (quotient (@species.setoid ℍ ω Γ)) → quotient (@species.setoid ℍ ω Γ)
    | [] := ⟦ nil ⟧
    | [A] := A
    | (A :: As) := mk A (from_list As)

    lemma from_append {Γ} :
      ∀ (A B : list (quotient (@species.setoid ℍ ω Γ)))
      , from_list (A ++ B) = mk (from_list A) (from_list B)
    | [] B := begin
        simp only [list.nil_append],
        from quot.induction_on (from_list B) (λ B, quot.sound (symm equiv.parallel_nil')),
      end
    | [A] [] := quot.induction_on A (λ A, quot.sound equiv.parallel_nil₂)
    | [A] (B :: Bs) := rfl
    | (A :: A' :: As) B := begin
        show mk A (from_list (A' :: As ++ B)) = mk (mk A (from_list (A' :: As))) (from_list B),
        rw (from_append (A' :: As) B),
        from assoc _ _ _,
      end

    private lemma from_cons {Γ} :
      ∀ (A : quotient (@species.setoid ℍ ω Γ)) {As Bs : list _}
      , from_list As = from_list Bs
      → from_list (A :: As) = from_list (A :: Bs)
    | A [] [] _ := refl _
    | A [] (B' :: Bs) eq := begin
        rcases quot.exists_rep A with ⟨ A, ⟨ _ ⟩ ⟩,
        simp only [from_list, symm eq],
        from quot.sound equiv.parallel_nil₂,
      end
    | A (A' :: As) [] eq := begin
        rcases quot.exists_rep A with ⟨ A, ⟨ _ ⟩ ⟩,
        simp only [from_list, eq],
        from quot.sound equiv.parallel_nil₁,
      end
    | A (A' :: As) (B' :: Bs') eq := by simp only [from_list, eq]

    lemma permute {Γ} :
      ∀ {As Bs : list (quotient (@species.setoid ℍ ω Γ))}
      , As ≈ Bs → from_list As = from_list Bs := λ _ _ perm, begin
      induction perm,

      case list.perm.nil { from refl _ },
      case list.perm.skip : A As Bs pm ih { from from_cons A ih },
      case list.perm.swap : A B As {
        rcases quot.exists_rep A with ⟨ A, ⟨ _ ⟩ ⟩,
        rcases quot.exists_rep B with ⟨ B, ⟨ _ ⟩ ⟩,

        cases As,
        case list.nil { from quot.sound equiv.parallel_symm },
        case list.cons {
          unfold from_list,
          from quotient.induction_on (from_list (As_hd :: As_tl))
            (λ _, quot.sound equiv.parallel_symm₁),
        },
      },
      case list.perm.trans : As Bs Cs ab bc ih_ab ih_bc { from trans ih_ab ih_bc }
    end
  end quot
end parallel

namespace choice
  lemma permute {Γ} :
    ∀ {As Bs : list (Σ' {f} (π : prefix_expr ℍ Γ f), species ℍ ω (f.apply Γ))}
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
  variables A A' B C : species ℍ ω Γ

  example : A ≈ (A |ₛ nil) := symm equiv.parallel_nil₁

  example : A ≈ (nil |ₛ A) := trans equiv.parallel_nil₂ equiv.parallel_symm

  example : A ≈ A' → (A |ₛ B) ≈ C → (A' |ₛ B) ≈ C := begin
    assume a eq,
    from trans (symm $ equiv.ξ_parallel₁ a) eq
  end
end examples

end species

/-- A quotient of all structurally congruent species. -/
def species' (ℍ : Type) (ω Γ : context) := quotient (@species.setoid ℍ ω Γ)

end cpi

#lint-
