import data.cpi.basic
import data.cpi.var

namespace cpi

namespace name
  def swap :
    ∀ {Γ} {M N : ℕ}
    , name (context.extend M (context.extend N Γ))
    → name (context.extend N (context.extend M Γ))
  | Γ M N (name.nil p) := name.extend (name.nil p)
  | Γ M N (name.extend (name.nil p)) := name.nil p
  | Γ M N (name.extend (name.extend n)) := name.extend (name.extend n)

  theorem swap.twice :
    ∀ {Γ} {M N : ℕ} {α : name (context.extend M (context.extend N Γ))}
    , swap (swap α) = α
  | Γ M N (name.nil p) := by unfold swap
  | Γ M N (name.extend (name.nil p)) := by unfold swap
  | Γ M N (name.extend (name.extend n)) := by unfold swap

  theorem swap.twice_id :
    ∀ {Γ} {M N : ℕ}
    , (λ (s : name (context.extend M (context.extend N Γ))), swap (swap s))
      = id
    | Γ M N := by { simp only [@swap.twice Γ M N], from rfl }
end name

namespace species
  inductive equiv : ∀ {Γ : context}, species Γ → species Γ → Prop
  -- ξ rules just map the insides
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
      ∀ {Γ} (π : prefix_expr Γ) {A A' : species (prefix_expr.augment π Γ)} {As As' : choices Γ},
        equiv A A'
      → equiv (choice As) (choice As')
      → equiv (choice (choices.cons π A As)) (choice (choices.cons π A' As'))

  -- And now we have our main equivalence rules. Note, in the non-symetric
  -- cases, we have two rules, for A ≡ f(A) and f(A) ≡ A. While this is a
  -- little ugly, the alternative "swap : equiv A B → equiv B A" rule, adds
  -- even more complexities.

  | nil_parallel₁ :
    ∀ {Γ} {A A' : species Γ}
    , equiv A A'
    → equiv (A |ₛ nil) A'
  | nil_parallel₂ :
    ∀ {Γ} {A A' : species Γ}
    , equiv A A'
    → equiv A' (A |ₛ nil)

  | parallel_symm :
    ∀ {Γ} {A A' B B' : species Γ}
    , equiv A A' → equiv B B'
    → equiv (A |ₛ B) (B' |ₛ A')
  | parallel_assoc₁ :
    ∀ {Γ} {A A' B B' C C' : species Γ}
    , equiv A A' → equiv B B' → equiv C C'
    → equiv ((A |ₛ B) |ₛ C) (A' |ₛ (B' |ₛ C'))
  | parallel_assoc₂ :
    ∀ {Γ} {A A' B B' C C' : species Γ}
    , equiv A A' → equiv B B' → equiv C C'
    → equiv (A' |ₛ (B' |ₛ C')) ((A |ₛ B) |ₛ C)

  | ν_parallel₁ :
    ∀ {Γ} (M : affinity) {A B B': species (context.extend M.arity Γ)} {A' : species Γ}
    , equiv A (subst name.extend A') → equiv B B'
    → equiv (ν(M) (A |ₛ B)) (A' |ₛ ν(M)B')
  | ν_parallel₂ :
    ∀ {Γ} (M : affinity) {A B B': species (context.extend M.arity Γ)} {A' : species Γ}
    , equiv A (subst name.extend A') → equiv B B'
    → equiv (A' |ₛ ν(M)B') (ν(M) (A |ₛ B))
  | ν_drop₁ :
    ∀ {Γ} (M : affinity) {A : species (context.extend M.arity Γ)} {A' : species Γ}
    , equiv A (subst name.extend A')
    → equiv (ν(M)A) A'
  | ν_drop₂ :
    ∀ {Γ} (M : affinity) {A : species (context.extend M.arity Γ)} {A' : species Γ}
    , equiv A (subst name.extend A')
    → equiv A' (ν(M)A)
  | ν_swap :
    ∀ {Γ} (M N : affinity)
      {A  : species (context.extend N.arity (context.extend M.arity Γ))}
      {A' : species (context.extend M.arity (context.extend N.arity Γ))}
    , equiv A (subst name.swap A')
    → @equiv Γ (ν(M)ν(N)A) (ν(N)ν(M)A')

  namespace equiv
    local infix ` ~ ` := equiv

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

    /-- Equivalence holds over substitution. -/
    protected theorem subst :
      ∀ {Γ Δ} {A B : species Γ} (ρ : name Γ → name Δ)
      , A ~ B
      → subst ρ A ~ subst ρ B
    := sorry

    /-- Equivalence is symmetric. -/
    protected theorem symm : ∀ {Γ} {A B : species Γ}, A ~ B → B ~ A
    | Γ ._ ._ ξ_nil := ξ_nil
    | Γ ._ ._ (ξ_parallel eq_a eq_b) := ξ_parallel (symm eq_a) (symm eq_b)
    | Γ ._ ._ (ξ_restriction M eq) := ξ_restriction M (symm eq)
    | Γ ._ ._ ξ_choice_nil := ξ_choice_nil
    | Γ ._ ._ (ξ_choice_cons π eq_a eq_as) := ξ_choice_cons π (symm eq_a) (symm eq_as)

    | Γ ._ ._ (nil_parallel₁ eq) := nil_parallel₂ eq
    | Γ ._ ._ (nil_parallel₂ eq) := nil_parallel₁ eq

    | Γ ._ ._ (parallel_symm eq_a eq_b) := parallel_symm (symm eq_b) (symm eq_a)
    | Γ ._ ._ (parallel_assoc₁ eq_a eq_b eq_c) := parallel_assoc₂ eq_a eq_b eq_c
    | Γ ._ ._ (parallel_assoc₂ eq_a eq_b eq_c) := parallel_assoc₁ eq_a eq_b eq_c

    | Γ ._ ._ (ν_parallel₁ M eq_a eq_b) := ν_parallel₂ M eq_a eq_b
    | Γ ._ ._ (ν_parallel₂ M eq_a eq_b) := ν_parallel₁ M eq_a eq_b
    | Γ ._ ._ (ν_drop₁ M eq_a) := ν_drop₂ M eq_a
    | Γ ._ ._ (ν_drop₂ M eq_a) := ν_drop₁ M eq_a
    | Γ ._ ._ (@ν_swap _ M N A A' eq) :=
        let eq' := symm eq in
        let h : A' ~ subst name.swap A := begin
          have x
            : subst name.swap (subst name.swap A') ~ subst name.swap A
            := equiv.subst name.swap eq',
          have is_eq
            : (subst name.swap (subst name.swap A') ~ subst name.swap A) = (A' ~ subst name.swap A),
            -- rw name.swap.twice_id,
            -- := name.swap.twice,
          rw [eq.symm name.swap.twice],
          sorry
        end in
        ν_swap N M h
    using_well_founded {
      rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ s, sizeof s.snd)⟩ ],
      dec_tac := tactic.fst_dec_tac,
    }

    instance : ∀ {Γ}, is_symm (species Γ) equiv := λ Γ, ⟨ @equiv.symm Γ ⟩

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
  end equiv
end species

end cpi
