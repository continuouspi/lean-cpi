import data.cpi.basic
import data.cpi.var

namespace cpi

namespace name
  def swap {Γ} {M N : ℕ}
    : name (context.extend M (context.extend N Γ))
    → name (context.extend N (context.extend M Γ))
  | (name.nil p) := name.extend (name.nil p)
  | (name.extend (name.nil p)) := name.nil p
  | (name.extend (name.extend n)) := name.extend (name.extend n)

  theorem swap.twice {Γ} {M N : ℕ} :
    ∀ {α : name (context.extend M (context.extend N Γ))}
    , swap (swap α) = α
  | (name.nil p) := by unfold swap
  | (name.extend (name.nil p)) := by unfold swap
  | (name.extend (name.extend n)) := by unfold swap

  theorem swap.twice_id {Γ} {M N : ℕ} : (@swap Γ M N ∘ swap) = id
    := by { simp only [function.comp, swap.twice], from rfl }

  theorem swap.ext_ext {Γ Δ} {ρ : name Γ → name Δ} {m n : ℕ}
    : (name.ext (name.ext ρ) ∘ name.swap)
    = (name.swap ∘ @name.ext _ _ (@name.ext _ _ ρ m) n) :=
    let h : ∀ α, (name.ext (name.ext ρ) ∘ name.swap) α
               = (name.swap ∘ @name.ext _ _ (@name.ext _ _ ρ m) n) α := λ α,
      match α with
      | name.nil p := by simp [name.swap, name.ext]
      | name.extend (name.nil p) := by simp [name.swap, name.ext]
      | name.extend (name.extend _) := by simp [name.swap, name.ext]
      end
    in funext h
end name

namespace species
  /-- An equivalency relationship over species.

      This can be viewed as a sequence of rewrite rules from one term to
      another.

      Rewrite rules are chained together using the equiv.chain construction,
      which means this structure proves equivalency by default.

      We do not have explicit refl or symm rules however. ξ rules provide
      projections into structures, which allow one to implement refl, and
      all non-symmetric rules end up having forwards and backwards versions -
      while this does lead to some duplication, it seems easier to reason
      about than having a generic "x_symm" rule.
  -/
  inductive equiv : ∀ {Γ : context} (A B : species Γ), Type
  -- Chain two rewrite rules together.
  | chain : ∀ {Γ} {A B C : species Γ}
          , equiv A B → equiv B C → equiv A C

  -- ξ rules act as projections into the body of a species.
  | ξ_nil : ∀ {Γ}, @equiv Γ nil nil
  | ξ_parallel :
      ∀ {Γ} {A A' B B' : species Γ}
      , equiv A A' → equiv B B'
      → equiv (A |ₛ B) (A' |ₛ B')
  | ξ_restriction :
      ∀ {Γ} (M : affinity) {A A' : species (context.extend (M.arity) Γ)}
      , equiv A A'
      → equiv (ν(M) A) (ν(M) A')
  | ξ_choice_nil : ∀ {Γ}, @equiv Γ (choice choices.nil) (choice choices.nil)
  | ξ_choice_cons :
      ∀ {Γ} {f} (π : prefix_expr Γ f) {A A' : species (f Γ)} {As As' : choices Γ},
        equiv A A'
      → equiv (choice As) (choice As')
      → equiv (choice (choices.cons π A As)) (choice (choices.cons π A' As'))

  -- | An element in the choice array can be swapped.
  | choice_swap :
    ∀ {Γ} {f g} (π₁ : prefix_expr Γ f) (π₂ : prefix_expr Γ g)
      {A : species (f Γ)} {B : species (g Γ)} {As : choices Γ}
    , equiv (choice (choices.cons π₁ A (choices.cons π₂ B As)))
            (choice (choices.cons π₂ B (choices.cons π₁ A As)))

  -- Species forms a commutative semigroup over parallel (and nil).
  | parallel_nil₁ : ∀ {Γ} {A : species Γ}, equiv (A |ₛ nil) A
  | parallel_nil₂ : ∀ {Γ} {A : species Γ}, equiv A (A |ₛ nil)
  | parallel_symm :   ∀ {Γ} {A B : species Γ}, equiv (A |ₛ B) (B |ₛ A)
  | parallel_assoc₁ : ∀ {Γ} {A B C : species Γ}, equiv ((A |ₛ B) |ₛ C) (A |ₛ (B |ₛ C))
  | parallel_assoc₂ : ∀ {Γ} {A B C : species Γ}, equiv (A |ₛ (B |ₛ C)) ((A |ₛ B) |ₛ C)

  -- Can move ν into a parallel branch when unused.
  | ν_parallel₁ :
    ∀ {Γ} (M : affinity) {A : species Γ} {B : species (context.extend M.arity Γ)}
    , equiv (ν(M) (subst name.extend A |ₛ B)) (A |ₛ ν(M)B)
  | ν_parallel₂ :
    ∀ {Γ} (M : affinity) {A : species Γ} {B : species (context.extend M.arity Γ)}
    , equiv (A |ₛ ν(M)B) (ν(M) (subst name.extend A |ₛ B))

  -- Can drop an unused ν
  | ν_drop₁ :
    ∀ {Γ} (M : affinity) {A : species Γ}
    , equiv (ν(M) subst name.extend A) A
  | ν_drop₂ :
    ∀ {Γ} (M : affinity) {A : species Γ}
    , equiv A (ν(M) subst name.extend A)

  -- Can swap two ν variables safely. Ideally this one could be
  -- a single rule, but the use of swap means it isn't.
  | ν_swap₁ :
    ∀ {Γ} (M N : affinity)
      {A : species (context.extend N.arity (context.extend M.arity Γ))}
    , @equiv Γ (ν(M)ν(N)A) (ν(N)ν(M) subst name.swap A)
  | ν_swap₂ :
    ∀ {Γ} (M N : affinity)
      {A : species (context.extend N.arity (context.extend M.arity Γ))}
    , @equiv Γ (ν(N)ν(M) subst name.swap A) (ν(M)ν(N)A)

  /-- Lower equivalence to the Prop level.

      Ideally equiv would be a Prop. However, one cannot write functions which
      map from a prop to a type, which means we cannot determine the size of
      an equivalence class. This means the termination checker is not aware of
      the size of equivalence classes, and so fails to verify recursive
      functions are well-formed.
  -/
  inductive equiv.wrap {Γ : context} (A B : species Γ) : Prop
  | intro : equiv A B → equiv.wrap

  namespace equiv
    local infix ` ~ `:51 := equiv

    /-- Equivalence is reflexative. -/
    protected theorem refl : ∀ {Γ} (A : species Γ), A ~ A
    | ._ nil := ξ_nil
    | Γ (A |ₛ B) := ξ_parallel (refl A) (refl B)
    | Γ (ν(M)A) := ξ_restriction M (refl A)
    | ._ (choice choices.nil) := ξ_choice_nil
    | Γ (choice (choices.cons π A As)) := ξ_choice_cons π (refl A) (refl (choice As))
    using_well_founded {
      rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ s, sizeof s.snd)⟩ ],
      dec_tac := tactic.fst_dec_tac,
    }

    private lemma subst_ext
      {Γ Δ} {ρ : name Γ → name Δ} {M : affinity} (A' : species Γ)
      : subst name.extend (subst ρ A')
      = subst (name.ext ρ) (subst (@name.extend _ M.arity) A')
    := by rw [subst_compose, ← name.ext_extend, subst_compose]

    private lemma subst_swap
      {Γ Δ} {ρ : name Γ → name Δ} {M N : affinity}
      (A' : species (context.extend M.arity (context.extend N.arity Γ)))
      : subst (name.ext (name.ext ρ)) (subst name.swap A')
      = subst name.swap (subst (name.ext (name.ext ρ)) A')
      := by rw [subst_compose, name.swap.ext_ext, subst_compose]

    /-- Equivalence holds over substitution. -/
    protected theorem subst_pres :
      ∀ {Γ Δ} {A B : species Γ} (ρ : name Γ → name Δ)
      , A ~ B
      → subst ρ A ~ subst ρ B
    | Γ Δ ._ ._ ρ (@chain _ A B C ab bc) := chain (subst_pres ρ ab) (subst_pres ρ bc)

    | Γ Δ ._ ._ ρ ξ_nil := by { unfold subst, from ξ_nil }
    | Γ Δ ._ ._ ρ (ξ_parallel eq_a eq_b) := begin
        unfold subst,
        from ξ_parallel (subst_pres ρ eq_a) (subst_pres ρ eq_b)
      end
    | Γ Δ ._ ._ ρ (ξ_restriction M eq) := begin
        unfold subst,
        from ξ_restriction M (subst_pres (name.ext ρ) eq)
      end
    | Γ Δ ._ ._ ρ ξ_choice_nil :=
      by { unfold subst subst.choice, from ξ_choice_nil }
    | Γ Δ ._ ._ ρ (@ξ_choice_cons _ f π A A' As As' eq_a eq_as) := begin
        simp [subst, subst.choice],
        have as : choice (subst.choice ρ As) ~ choice (subst.choice ρ As'),
          have h : subst ρ (choice As) ~ subst ρ (choice As') := subst_pres ρ eq_as,
          unfold subst at h, assumption,
        from ξ_choice_cons _ (subst_pres (prefix_expr.ext π ρ) eq_a) as,
      end

    | Γ Δ ._ ._ ρ (@choice_swap _ f g π₁ π₂ A B As) := begin
        simp only [subst, subst.choice],
        from choice_swap (prefix_expr.subst ρ π₁) (prefix_expr.subst ρ π₂)
      end

    | Γ Δ ._ ._ ρ parallel_nil₁ := by { unfold subst, from parallel_nil₁ }
    | Γ Δ ._ ._ ρ parallel_nil₂ := by { unfold subst, from parallel_nil₂ }
    | Γ Δ ._ ._ ρ parallel_symm := by { unfold subst, from parallel_symm }
    | Γ Δ ._ ._ ρ parallel_assoc₁ := by { unfold subst, from parallel_assoc₁ }
    | Γ Δ ._ ._ ρ parallel_assoc₂ := by { unfold subst, from parallel_assoc₂ }

    | Γ Δ ._ ._ ρ (@ν_parallel₁ _ M A B) := begin
        unfold subst,
        rw ← subst_ext A,
        from ν_parallel₁ M,
      end
    | Γ Δ ._ ._ ρ (@ν_parallel₂ _ M A B) := begin
        unfold subst,
        rw ← subst_ext A,
        from ν_parallel₂ M,
      end
    | Γ Δ ._ ._ ρ (@ν_drop₁ _ M A) := begin
        unfold subst,
        rw ← subst_ext A,
        from ν_drop₁ M
      end
    | Γ Δ ._ ._ ρ (@ν_drop₂ _ M A) := begin
        unfold subst,
        rw ← subst_ext A,
        from ν_drop₂ M
      end
    | Γ Δ ._ ._ ρ (@ν_swap₁ _ M N A) := begin
        unfold subst,
        rw subst_swap A,
        from ν_swap₁ M N
      end
    | Γ Δ ._ ._ ρ (@ν_swap₂ _ M N A) := begin
        unfold subst,
        rw subst_swap A,
        from ν_swap₂ M N
      end

    /-- Equivalence is symmetric. -/
    protected theorem symm : ∀ {Γ} {A B : species Γ}, A ~ B → B ~ A
    | Γ ._ ._ (chain ab bc) := chain (symm bc) (symm ab)

    | Γ ._ ._ ξ_nil := ξ_nil
    | Γ ._ ._ (ξ_parallel eq_a eq_b) := ξ_parallel (symm eq_a) (symm eq_b)
    | Γ ._ ._ (ξ_restriction M eq) := ξ_restriction M (symm eq)
    | Γ ._ ._ ξ_choice_nil := ξ_choice_nil
    | Γ ._ ._ (ξ_choice_cons π eq_a eq_as) := ξ_choice_cons π (symm eq_a) (symm eq_as)

    | Γ ._ ._ (choice_swap π₁ π₂) := choice_swap π₂ π₁

    | Γ ._ ._ parallel_nil₁ := parallel_nil₂
    | Γ ._ ._ parallel_nil₂ := parallel_nil₁
    | Γ ._ ._ parallel_symm := parallel_symm
    | Γ ._ ._ parallel_assoc₁ := parallel_assoc₂
    | Γ ._ ._ parallel_assoc₂ := parallel_assoc₁

    | Γ ._ ._ (ν_parallel₁ M) := ν_parallel₂ M
    | Γ ._ ._ (ν_parallel₂ M) := ν_parallel₁ M
    | Γ ._ ._ (ν_drop₁ M) := ν_drop₂ M
    | Γ ._ ._ (ν_drop₂ M) := ν_drop₁ M
    | Γ ._ ._ (ν_swap₁ M N) := ν_swap₂ M N
    | Γ ._ ._ (ν_swap₂ M N) := ν_swap₁ M N

    protected theorem trans : ∀ {Γ} {A B C : species Γ}, A ~ B → B ~ C → A ~ C := @chain

    instance is_equiv : ∀ {Γ : context}, is_equiv (species Γ) wrap
    | Γ := { refl := λ x, ⟨ equiv.refl x ⟩,
             symm := λ _ _ ⟨ eq ⟩, ⟨ equiv.symm eq ⟩,
             trans := λ _ _ _ ⟨ ab ⟩ ⟨ bc ⟩, ⟨ equiv.trans ab bc ⟩ }

  end equiv

  instance : ∀ {Γ : context}, setoid (species Γ)
  | Γ := ⟨ equiv.wrap, ⟨ equiv.is_equiv.refl, equiv.is_equiv.symm, equiv.is_equiv.trans ⟩ ⟩

  /- Just a couple of sanity checks for verifying equivalence proves what it
     does.-/
  section examples
    variable Γ : context
    variables A A' B C : species Γ

    example : A ≈ (A |ₛ nil) := wrap.intro equiv.parallel_nil₂

    example : A ≈ (nil |ₛ A) :=
      trans (wrap.intro equiv.parallel_nil₂) (wrap.intro equiv.parallel_symm)

    example : A ≈ A' → (A |ₛ B) ≈ C → (A' |ₛ B) ≈ C := λ ⟨ a ⟩ ⟨ eq ⟩,
      trans ⟨ equiv.ξ_parallel (equiv.symm a) (equiv.refl B) ⟩ ⟨ eq ⟩
  end examples
end species

end cpi
