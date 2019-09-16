import data.cpi.basic
import data.cpi.var
import data.rule_equiv
import tactic.known_induct

namespace cpi

namespace species
  /-- A chain of rewrite rule, to transform a species from one kind to another
      equivalent one. -/
  inductive equiv : ∀ {Γ : context} (A B : species Γ), Prop
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
      → equiv (choice (choices.cons π A As)) (choice (choices.cons π A' As))

  -- | An element in the choice array can be swapped.
  | choice_swap
      {Γ} {f g} (π₁ : prefix_expr Γ f) (π₂ : prefix_expr Γ g)
      {A : species (f Γ)} {B : species (g Γ)} {As : choices Γ}
    : equiv (choice (choices.cons π₁ A (choices.cons π₂ B As)))
              (choice (choices.cons π₂ B (choices.cons π₁ A As)))

  -- Species forms a commutative monoid using parallel.
  | parallel_nil   : ∀ {Γ} {A : species Γ},     equiv (A |ₛ nil) A
  | parallel_symm  : ∀ {Γ} {A B : species Γ},   equiv (A |ₛ B) (B |ₛ A)
  | parallel_assoc : ∀ {Γ} {A B C : species Γ}, equiv ((A |ₛ B) |ₛ C) (A |ₛ (B |ₛ C))

  | ν_parallel
      {Γ} (M : affinity) {A : species Γ} {B : species (context.extend M.arity Γ)}
    : equiv (ν(M) (subst name.extend A |ₛ B)) (A |ₛ ν(M)B)
  | ν_drop
      {Γ} (M : affinity) {A : species Γ}
    : equiv (ν(M) (subst name.extend A)) A
  | ν_swap
      {Γ} (M N : affinity)
      {A  : species (context.extend N.arity (context.extend M.arity Γ))}
    : @equiv Γ (ν(M)ν(N) A) (ν(N)ν(M) subst name.swap A)


  local infix ` ~ `:51 := equiv

  instance {Γ} : is_equiv (species Γ) equiv :=
    { refl := @equiv.refl Γ, symm := @equiv.symm Γ, trans := @equiv.trans Γ }
  instance {Γ} : is_refl (species Γ) equiv := ⟨ λ _, equiv.refl ⟩
  instance {Γ} : setoid (species Γ) :=
    ⟨ equiv, ⟨ @equiv.refl Γ, @equiv.symm Γ, @equiv.trans Γ ⟩ ⟩

  -- -- Somewhat odd instance, but required for transitivity of the operator form.
  instance setoid.is_equiv {Γ} : is_equiv (species Γ) has_equiv.equiv :=
    species.is_equiv

  namespace equiv
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

    protected def subst :
       ∀ {Γ Δ} {A B : species Γ} (ρ : name Γ → name Δ)
       , A ~ B → subst ρ A ~ subst ρ B
      := begin
        intros _Γ _Δ _A _B _ρ _eq,
        known_induction species.equiv @equiv.rec_on
          (λ Γ A B, Π {Δ} (ρ : name Γ → name Δ), subst ρ A ~ subst ρ B)
          _Γ _A _B _eq,

        case refl : Γ A Δ ρ { from refl },
        case trans : Γ A B C ab bc ih_ab ih_bc Δ ρ { from trans (ih_ab ρ) (ih_bc ρ) },
        case symm : Γ A B eq ih Δ ρ { from symm (ih ρ) },

        -- Projection
        case ξ_parallel₁ : Γ A A' B eq ih Δ ρ {
          unfold species.subst, from ξ_parallel₁ (ih ρ)
        },
        case ξ_parallel₂ : Γ A A' B eq ih Δ ρ {
          unfold species.subst, from ξ_parallel₂ (ih ρ)
        },
        case ξ_restriction : Γ M A A' eq ih Δ ρ {
          unfold species.subst,
          from ξ_restriction M (ih (name.ext ρ))
        },
        case ξ_choice_cons : Γ f π A A' As eq ih Δ ρ {
          unfold species.subst species.subst.choice,
          from ξ_choice_cons (prefix_expr.subst ρ π) (ih (prefix_expr.ext π ρ))
        },

        -- Choice
        case choice_swap : Γ f g π₁ π₂ A B As Δ ρ {
          simp only [species.subst, species.subst.choice],
          from choice_swap _ _
        },

        -- Parallel
        case parallel_nil : Γ A Δ ρ { unfold species.subst, from parallel_nil },
        case parallel_symm : Γ A B Δ ρ { unfold species.subst, from parallel_symm },
        case parallel_assoc : Γ A B C Δ ρ { unfold species.subst, from parallel_assoc },

        -- Restriction
        case ν_parallel : Γ M A B Δ ρ {
          unfold species.subst, rw ← subst_ext _, from ν_parallel M
        },
        case ν_drop : Γ M A Δ ρ {
          unfold species.subst, rw ← subst_ext _, from ν_drop M
        },
        case ν_swap : Γ M N A Δ ρ {
          unfold species.subst, rw subst_swap _, from ν_swap M N
        }
      end

      def parallel_symm₁ {Γ} {A B C : species Γ} : (A |ₛ B |ₛ C) ≈ (B |ₛ A |ₛ C) :=
        calc  (A |ₛ (B |ₛ C))
            ≈ ((A |ₛ B) |ₛ C) : symm (@parallel_assoc _ A B C)
        ... ≈ ((B |ₛ A) |ₛ C) : ξ_parallel₁ parallel_symm
        ... ≈ (B |ₛ (A |ₛ C)) : parallel_assoc

      def parallel_symm₂ {Γ} {A B C : species Γ} : ((A |ₛ B) |ₛ C) ≈ ((A |ₛ C) |ₛ B) :=
        calc  ((A |ₛ B) |ₛ C)
            ≈ (A |ₛ (B |ₛ C)) : parallel_assoc
        ... ≈ (A |ₛ (C |ₛ B)) : ξ_parallel₂ parallel_symm
        ... ≈ ((A |ₛ C) |ₛ B) : symm parallel_assoc

      def ν_parallel' {Γ} (M : affinity) {A : species (context.extend M.arity Γ)} {B : species Γ}
        : (ν(M) (A |ₛ subst name.extend B)) ≈ ((ν(M)A) |ₛ B) :=
        calc  (ν(M) A |ₛ subst name.extend B)
            ≈ (ν(M) subst name.extend B |ₛ A) : ξ_restriction M parallel_symm
        ... ≈ (B |ₛ ν(M) A) : ν_parallel M
        ... ≈ ((ν(M) A) |ₛ B) : parallel_symm
  end equiv

  section examples
    variable Γ : context
    variables A A' B C : species Γ

    example : A ≈ (A |ₛ nil) := symm equiv.parallel_nil

    example : A ≈ (nil |ₛ A) :=
      trans
        (symm equiv.parallel_nil)
        equiv.parallel_symm

    example : A ~ A' → (A |ₛ B) ≈ C → (A' |ₛ B) ≈ C := begin
      assume a eq,
      from trans (symm $ equiv.ξ_parallel₁ a) eq
    end
  end examples
end species

-- namespace tactic
--   open tactic

--   private meta def collect_add_args : expr → list expr
--   | `(%%a |ₛ %%b) := collect_add_args a ++ collect_add_args b
--   | e             := [e]

--   -- private meta def prove_equiv_by_perm (a b : expr) : tactic expr :=
--   -- (is_def_eq a b >> to_expr ``(eq.refl %%a))
--   -- <|>
--   -- perm_ac (get_add_fn a) `(nat.add_assoc) `(nat.add_comm) a b

--   private meta def mk_par : list expr → tactic expr
--   | []      := to_expr ``(species.nil)
--   | [a]     := return a
--   | (a::as) := do
--     rs ← mk_par as,
--     to_expr ``(%%a |ₛ %%rs)

--   private meta def cancel_parallel : tactic unit := do
--     `(%%lhs ≈ %%rhs) ← target,
--     ty ← infer_type lhs >>= whnf,
--     guard (ty = `(nat)),
--     let lhs_args := collect_add_args lhs,
--     let rhs_args := collect_add_args rhs,
--     let common   := lhs_args.bag_inter rhs_args,
--     if common = [] then return ()
--     else do
--       let lhs_rest := lhs_args.diff common,
--       let rhs_rest := rhs_args.diff common,
--       new_lhs    ← mk_par (list.qsort expr.lt lhs_rest),
--       new_rhs    ← mk_par (list.qsort expr.lt rhs_rest),
--       lhs_pr     ← prove_eq_by_perm lhs new_lhs,
--       rhs_pr     ← prove_eq_by_perm rhs new_rhs,
--       target_pr  ← to_expr ``(congr (congr_arg (≈) %%lhs_pr) %%rhs_pr),
--       new_target ← to_expr ``(%%new_lhs ≈ %%new_rhs),
--       replace_target new_target target_pr

--   -- meta def species_equiv_parallel : (parse expr)

-- end tactic

end cpi
