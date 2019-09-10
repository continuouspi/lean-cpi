import data.cpi.prefix_expr
import data.list.sort

namespace cpi

/-- An affinity network.

    This is composed of $arity$ names, and a partial function $f$ which defines
    the affinities between elements of this matrix.
-/
structure affinity := affinity ::
    (arity : ℕ)
    (f : fin arity → fin arity → option ℝ≥0)

/-- The set of species, defining invocation, guarded choice, parallel composition
    and restriction.
-/
inductive species
| nil : species
| choice : list (prefix_expr × species) → species
| parallel : species → species → species
| restriction : affinity → species → species

namespace species
    reserve infixr ` |ₛ ` :50
    infixr ` |ₛ ` := parallel

    notation `ν(` m `) ` a := restriction m a

    section free_variables
      def well_formed : context → species → Prop
      | Γ nil := true
      | Γ (A |ₛ B) := well_formed Γ A ∧ well_formed Γ B
      | Γ (ν(M)A) := well_formed (context.extend M.arity Γ) A
      | Γ (choice []) := true
      | Γ (choice ((π, A) :: As)) :=
          prefix_expr.well_formed Γ π ∧ well_formed (prefix_expr.augment Γ π) A ∧
          well_formed Γ (choice As)
      using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, species.sizeof (psigma.snd x))⟩ ] }

      /-- Increases all variables by one. -/
      mutual def subst, subst.choice
      with subst : (lvl → lvl) → species → species
      | ρ nil := nil
      | ρ (A |ₛ B) := subst ρ A |ₛ subst ρ B
      | ρ ν(M)A := ν(M)(subst (name.ext ρ) A)
      | ρ (choice As) := choice (subst.choice ρ As)
      with subst.choice : (lvl → lvl) → list (prefix_expr × species) → list (prefix_expr × species)
      | ρ [] := []
      | ρ ((π, A) :: As) := (prefix_expr.subst ρ π, subst (prefix_expr.ext ρ π) A) :: subst.choice ρ As

      private theorem subst.choice_eq :
        ∀ {As :  list (prefix_expr × species)} {ρ}
        , subst ρ (choice As) = choice (subst.choice ρ As)
      | As ρ := by unfold subst

      /-- The proof that raising a term preserves whether it is free. -/
      protected theorem subst.preserves_wf :
        Π {Γ Δ : context} {ρ : lvl → lvl}
        , (∀ (α : name), name.well_formed Γ α → name.well_formed Δ (name.subst ρ α))
        → ∀ (A : species), well_formed Γ A → well_formed Δ (subst ρ A)
      | Γ Δ ρ imp nil wf := by { unfold well_formed subst }
      | Γ Δ ρ imp (A |ₛ B) wf := begin
          unfold well_formed subst at wf ⊢,
          from and.imp (subst.preserves_wf imp A) (subst.preserves_wf imp B) wf
        end
      | Γ Δ ρ imp (ν(M)A) wf := begin
          unfold well_formed subst at wf ⊢,
          from subst.preserves_wf (name.ext.well_formed imp) A wf,
        end
      | Γ Δ ρ imp (choice []) wf := by { unfold well_formed subst subst.choice }
      | Γ Δ ρ imp (choice ((π, A) :: As)) wf := begin
          unfold well_formed subst subst.choice prefix_expr.subst at wf ⊢,
          rcases wf with ⟨ wf_pi, ⟨ wf_a, wf_as ⟩ ⟩,

          have wf_pi' : prefix_expr.well_formed Δ (prefix_expr.subst ρ π)
            := prefix_expr.subst.well_formed imp wf_pi,
          have wf_a' : well_formed (prefix_expr.augment Δ (prefix_expr.subst ρ π)) (subst (prefix_expr.ext ρ π) A),
            rw [symm prefix_expr.subst_augment], clear wf_pi wf_pi' wf_as,
            from subst.preserves_wf (prefix_expr.ext.well_formed imp) A wf_a,
          have wf_as' : well_formed Δ (choice (subst.choice ρ As)),
            rw [symm subst.choice_eq],
            from subst.preserves_wf imp (choice As) wf_as,
          from and.intro wf_pi' (and.intro wf_a' wf_as')
        end
      using_well_founded { rel_tac := λ _ _,
        `[exact ⟨_, measure_wf (λ (x : Σ' (Γ Δ : context) (ρ : lvl → lvl)
                                          (a : ∀ (α : name), name.well_formed Γ α → name.well_formed Δ (name.subst ρ α))
                                          (A : species),
                                          well_formed Γ A),
          species.sizeof x.snd.snd.snd.snd.fst)⟩ ] }
    end free_variables

    def swap : lvl → lvl
    | nat.zero := nat.succ nat.zero
    | (nat.succ nat.zero) := nat.zero
    | (nat.succ (nat.succ x)) := nat.succ (nat.succ x)

    def swap.twice : ∀ {n}, swap (swap n) = n
    | nat.zero := by unfold swap
    | (nat.succ nat.zero) := by unfold swap
    | (nat.succ (nat.succ x)) := by unfold swap

    inductive equiv : species → species → Prop
      -- ξ rules just map the insides
      | ξ_nil : equiv nil nil
      | ξ_parallel :
          ∀ {A A' B B' : species}
          , equiv A A' → equiv B B'
          → equiv (A |ₛ B) (A' |ₛ B')
      | ξ_restriction :
          ∀ {A A' : species} (M : affinity)
          , equiv A A'
          → equiv (ν(M) A) (ν(M) A')
      | ξ_choice_nil : equiv (choice []) (choice [])
      | ξ_choice_cons :
          ∀ {A A' : species} {As As' : list (prefix_expr × species)} (π : prefix_expr),
            equiv A A'
          → equiv (choice As) (choice As')
          → equiv (choice ((π, A) :: As)) (choice ((π, A') :: As'))

      -- And now we have our main equivalence rules. Note, in the non-symetric
      -- cases, we have two rules, for A ≡ f(A) and f(A) ≡ A. While this is a
      -- little ugly, the alternative seems to be some general
      -- "swap : equiv A B → equiv B A" rule, which adds even more complexities.

      | nil_parallel₁ :
        ∀ {A A' : species}
        , equiv A A'
        → equiv (A |ₛ nil) A'
      | nil_parallel₂ :
        ∀ {A A' : species}
        , equiv A A'
        → equiv A' (A |ₛ nil)

      | parallel_symm :
        ∀ {A A' B B' : species}
        , equiv A A' → equiv B B'
        → equiv (A |ₛ B) (B' |ₛ A')
      | parallel_assoc₁ :
        ∀ {A A' B B' C C' : species}
        , equiv A A' → equiv B B' → equiv C C'
        → equiv ((A |ₛ B) |ₛ C) (A' |ₛ (B' |ₛ C'))
      | parallel_assoc₂ :
        ∀ {A A' B B' C C' : species}
        , equiv A A' → equiv B B' → equiv C C'
        → equiv (A' |ₛ (B' |ₛ C')) ((A |ₛ B) |ₛ C)

      | ν_parallel₁ :
        ∀ {A A' B B': species} (M : affinity)
        , equiv A (subst nat.succ A') → equiv B B' → (∀ {Γ}, well_formed (context.extend M.arity Γ) A ↔ well_formed Γ A')
        → equiv (ν(M) (A |ₛ B)) (A' |ₛ ν(M)B')
      | ν_parallel₂ :
        ∀ {A A' B B': species} (M : affinity)
        , equiv A (subst nat.succ A') → equiv B B' → (∀ {Γ}, well_formed (context.extend M.arity Γ) A ↔ well_formed Γ A')
        → equiv (A' |ₛ ν(M)B') (ν(M) (A |ₛ B))
      | ν_drop₁ :
        ∀ {A A' : species} (M : affinity)
        , equiv A (subst nat.succ A') → (∀ {Γ}, well_formed (context.extend M.arity Γ) A ↔ well_formed Γ A')
        → equiv (ν(M)A) A'
      | ν_drop₂ :
        ∀ {A A' : species} (M : affinity)
        , equiv A (subst nat.succ A') → (∀ {Γ}, well_formed (context.extend M.arity Γ) A ↔ well_formed Γ A')
        → equiv A' (ν(M)A)
      | ν_swap :
        ∀ {A A' : species} (M N : affinity)
        , equiv A (subst swap A')
        → equiv (ν(M)ν(N)A) (ν(N)ν(M)A')

    namespace equiv
        local infix ` ~ ` := equiv

        protected theorem refl : ∀ (A : species), A ~ A
            | nil := ξ_nil
            | (A |ₛ B) := ξ_parallel (refl A) (refl B)
            | (ν(M)A) := ξ_restriction M (refl A)
            | (choice []) := ξ_choice_nil
            | (choice ((π, A) :: As)) := ξ_choice_cons π (refl A) (refl (choice As))

        protected theorem symm : ∀ {A B : species}, A ~ B → B ~ A
        | ._ ._ ξ_nil := ξ_nil
        | ._ ._ (ξ_parallel eq_a eq_b) := ξ_parallel (symm eq_a) (symm eq_b)
        | ._ ._ (ξ_restriction M eq) := ξ_restriction M (symm eq)
        | ._ ._ ξ_choice_nil := ξ_choice_nil
        | ._ ._ (ξ_choice_cons π eq_a eq_as) := ξ_choice_cons π (symm eq_a) (symm eq_as)

        | ._ ._ (nil_parallel₁ eq) := nil_parallel₂ eq
        | ._ ._ (nil_parallel₂ eq) := nil_parallel₁ eq

        | ._ ._ (parallel_symm eq_a eq_b) := parallel_symm (symm eq_b) (symm eq_a)
        | ._ ._ (parallel_assoc₁ eq_a eq_b eq_c) := parallel_assoc₂ eq_a eq_b eq_c
        | ._ ._ (parallel_assoc₂ eq_a eq_b eq_c) := parallel_assoc₁ eq_a eq_b eq_c

        | ._ ._ (ν_parallel₁ M eq_a eq_b wf) := ν_parallel₂ M eq_a eq_b @wf
        | ._ ._ (ν_parallel₂ M eq_a eq_b wf) := ν_parallel₁ M eq_a eq_b @wf
        | ._ ._ (ν_drop₁ M eq_a wf) := ν_drop₂ M eq_a @wf
        | ._ ._ (ν_drop₂ M eq_a wf) := ν_drop₁ M eq_a @wf
        | ._ ._ (@ν_swap A A' M N eq) := begin
            have eq' := symm eq,
            have h : A' ~ subst swap A, sorry
            from ν_swap N M _
          end

        instance : is_symm species equiv := ⟨ @equiv.symm ⟩

        -- protected theorem trans : ∀ {A B C : species}, A ~ B → B ~ C → A ~ C
        -- -- -- We have to unroll each case, as otherwise the totality checker times out.
        -- -- | nil s2 s3 eq_12 eq_23 :=
        -- --   match s2, s3, eq_12, eq_23 with
        -- --   | nil, nil, ξ_nil, ξ_nil := ξ_nil
        -- --   end
        -- -- | (_ |ₛ _) s2 s3 eq_12 eq_23 :=
        -- --   match s2, s3, eq_12, eq_23 with
        -- --   | _ |ₛ _, _ |ₛ _, ξ_parallel eq_a12 eq_b12, ξ_parallel eq_a23 eq_b23 :=
        -- --     ξ_parallel (trans eq_a12 eq_a23) (trans eq_b12 eq_b23)
        -- --   -- | _, _, eq_12, eq_23 with
        -- --   end
        -- -- | (ν(_)_) s2 s3 eq_12 eq_23 :=
        -- --     match s2, s3, eq_12, eq_23 with
        -- --     | ν(_)_, ν(_)_, ξ_restriction M eq_12, ξ_restriction _ eq_23 :=
        -- --          ξ_restriction M (trans eq_12 eq_23)
        -- --     end
        -- -- | (choice []) s2 s3 eq_12 eq_23 :=
        -- --   match s2, s3, eq_12, eq_23 with
        -- --   | choice [], choice [], ξ_choice_nil, ξ_choice_nil := ξ_choice_nil
        -- --   end
        -- -- | (choice ((π, A1) :: As)) s2 s3 eq_12 eq_23 :=
        -- --     match s2, s3, eq_12, eq_23 with
        -- --     | choice ((_, _)::_), choice ((_, _)::_), ξ_choice_cons _ eq_a12 eq_as12, ξ_choice_cons _ eq_a23 eq_as23 :=
        -- --       ξ_choice_cons π (trans eq_a12 eq_a23) (trans eq_as12 eq_as23)
        -- --     end


        -- -- | nil nil nil ξ_nil ξ_nil := ξ_nil
        -- -- | (A1 |ₛ B1) (A2 |ₛ B2) (A3 |ₛ B3) (ξ_parallel eq_a12 eq_b12) (ξ_parallel eq_a23 eq_b23) :=
        -- --     ξ_parallel (trans eq_a12 eq_a23) (trans eq_b12 eq_b23)
        -- -- | (ν(_)A1) (ν(_)A2) (ν(_)A3) (ξ_restriction M eq_12) (ξ_restriction _ eq_23) :=
        -- --     ξ_restriction M (trans eq_12 eq_23)
        -- -- | (choice []) (choice []) (choice[]) ξ_choice_nil ξ_choice_nil := ξ_choice_nil
        -- -- | (choice ((_, A1)::As1)) (choice ((_, A2)::As2)) (choice ((_, A3)::As3))
        -- --   (ξ_choice_cons π eq_a12 eq_as12) (ξ_choice_cons _ eq_a23 eq_as23) :=
        -- --     ξ_choice_cons π (trans eq_a12 eq_a23) (trans eq_as12 eq_as23)
        -- -- | _ _ _ _ _ := sorry

        -- | ._ ._ ._ ξ_nil ξ_nil := ξ_nil
        -- | ._ ._ ._ (ξ_parallel eq_a12 eq_b12) (ξ_parallel eq_a23 eq_b23) :=
        --     ξ_parallel (trans eq_a12 eq_a23) (trans eq_b12 eq_b23)
        -- | ._ ._ ._ (ξ_restriction M eq_12) (ξ_restriction _ eq_23) :=
        --     ξ_restriction M (trans eq_12 eq_23)
        -- | ._ ._ ._ ξ_choice_nil ξ_choice_nil := ξ_choice_nil
        -- | ._ ._ ._ (ξ_choice_cons π eq_a12 eq_as12) (ξ_choice_cons _ eq_a23 eq_as23) :=
        --     ξ_choice_cons π (trans eq_a12 eq_a23) (trans eq_as12 eq_as23)

        protected theorem preserves_wf : ∀ {A B : species} {Γ : context}, A ~ B → well_formed Γ A → well_formed Γ B
        | ._ ._ Γ ξ_nil wf := by { unfold well_formed }
        | ._ ._ Γ (@ξ_parallel A A' B B' eq_a eq_b) wf := begin
            unfold well_formed at wf ⊢,
            from and.imp (preserves_wf eq_a) (preserves_wf eq_b) wf
          end
        | ._ ._ Γ (@ξ_restriction A A' M eq) wf := begin
            unfold well_formed at wf ⊢,
            from preserves_wf eq wf,
          end
        | ._ ._ Γ ξ_choice_nil wf := by { unfold well_formed }
        | ._ ._ Γ (@ξ_choice_cons A A' As As' π eq_a eq_as) wf := begin
            unfold well_formed at wf ⊢,
            from and.imp_right (and.imp (preserves_wf eq_a) (preserves_wf eq_as)) wf
          end
        | ._ ._ Γ (@nil_parallel₁ A A' eq_a) wf := begin
            unfold well_formed at wf ⊢, simp only [and_true] at wf,
            from preserves_wf eq_a wf
          end
        | ._ ._ Γ (@nil_parallel₂ A A' eq_a) wf := begin
            unfold well_formed at wf ⊢, simp only [and_true] at ⊢,
            from preserves_wf (symm eq_a) wf
          end
        | ._ ._ Γ (@parallel_symm A A' B B' eq_a eq_b) wf := begin
            unfold well_formed at wf ⊢,
            from and.swap (and.imp (preserves_wf eq_a) (preserves_wf eq_b) wf)
          end
        | ._ ._ Γ (@parallel_assoc₁ A A' B B' C C' eq_a eq_b eq_c) wf := begin
            unfold well_formed at wf ⊢,
            have wf' : well_formed Γ A ∧ (well_formed Γ B ∧ well_formed Γ C) := iff.mp and.assoc wf,
            from and.imp (preserves_wf eq_a) (and.imp (preserves_wf eq_b) (preserves_wf eq_c)) wf'
          end
        | ._ ._ Γ (@parallel_assoc₂  A A' B B' C C' eq_a eq_b eq_c) wf := begin
            unfold well_formed at wf ⊢,
            have wf' : (well_formed Γ A' ∧ well_formed Γ B') ∧ well_formed Γ C' := iff.mpr and.assoc wf,
            from and.imp (and.imp (preserves_wf (symm eq_a)) (preserves_wf (symm eq_b)))
                         (preserves_wf (symm eq_c)) wf'
          end
        | ._ ._ Γ (@ν_parallel₁ A A' B B' M eq_a eq_b wf_imp) wf := begin
            unfold well_formed at wf ⊢, cases wf with wf_a wf_b,
            from and.intro (wf_imp.mp wf_a) (preserves_wf eq_b wf_b),
          end
        | ._ ._ Γ (@ν_parallel₂ A A' B B' M eq_a eq_b wf_imp) wf := begin
            unfold well_formed at wf ⊢, cases wf with wf_a wf_b,
            from and.intro (wf_imp.mpr wf_a) (preserves_wf (symm eq_b) wf_b),
          end
        | ._ ._ Γ (@ν_drop₁ A A' M eq wf_imp) wf := begin
            unfold well_formed at wf ⊢,
            from wf_imp.mp wf
          end
        | ._ ._ Γ (ν_drop₂ M eq wf_imp) wf := begin
            unfold well_formed at wf ⊢,
            from wf_imp.mpr wf
          end
        | ._ ._ Γ (ν_swap M N _) wf := sorry
    end equiv

    instance : setoid species := sorry
end species

end cpi
