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

      Ideally this should be a type, but it means we do not have
      acess to sizeof, which makes it impossible to reasonably argue
      about terms. -/
  inductive equiv : ∀ {Γ : context} (A B : species Γ), Type
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
      ∀ {Γ} {f} (π : prefix_expr Γ f) {A A' : species (f Γ)} {As As' : choices Γ},
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

  /-- Lower equivalence to the Prop level. -/
  inductive is_equiv {Γ : context} (A B : species Γ) : Prop
  | intro : equiv A B → is_equiv

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

    @[inline] private def depth : ∀ {Γ} {A B : species Γ}, A ~ B → ℕ
    | ._ ._ ._ ξ_nil := 1
    | ._ ._ ._ (ξ_parallel eq_a eq_b) := 1 + depth eq_a + depth eq_b
    | ._ ._ ._ (ξ_restriction _ eq) := 1 + depth eq
    | ._ ._ ._ ξ_choice_nil := 1
    | ._ ._ ._ (ξ_choice_cons _ eq_a eq_as) := 1 + depth eq_a + depth eq_as

    | ._ ._ ._ (nil_parallel₁ eq) := 1 + depth eq
    | ._ ._ ._ (nil_parallel₂ eq) := 1 + depth eq

    | ._ ._ ._ (parallel_symm eq_a eq_b) := 1 + depth eq_b + depth eq_a
    | ._ ._ ._ (parallel_assoc₁ eq_a eq_b eq_c) := 1 + depth eq_a + depth eq_b + depth eq_c
    | ._ ._ ._ (parallel_assoc₂ eq_a eq_b eq_c) := 1 + depth eq_a + depth eq_b + depth eq_c

    | ._ ._ ._ (ν_parallel₁ M eq_a eq_b) := 1 + depth eq_a + depth eq_b
    | ._ ._ ._ (ν_parallel₂ M eq_a eq_b) := 1 + depth eq_a + depth eq_b
    | ._ ._ ._ (ν_drop₁ M eq_a) := 1 + depth eq_a
    | ._ ._ ._ (ν_drop₂ M eq_a) := 1 + depth eq_a
    | ._ ._ ._ (ν_swap M N eq) := 1 + depth eq

    -- set_option profiler true

    meta def depth_tactic : tactic unit := do
      well_founded_tactics.unfold_wf_rel,
      well_founded_tactics.unfold_sizeof,
      tactic.dunfold_target [``depth],
      tactic.trace_state,
      tactic.try well_founded_tactics.cancel_nat_add_lt,
      tactic.trace_state,
      well_founded_tactics.trivial_nat_lt

    private lemma subst_ext
      {Γ Δ} {ρ : name Γ → name Δ} {M : affinity}
      (A : species (context.extend M.arity Γ)) (A' : species Γ)
      : subst name.extend (subst ρ A')
      = subst (name.ext ρ) (subst (@name.extend _ M.arity) A')
    := by rw [subst_compose, ← name.ext_extend, subst_compose]

    private lemma subst_swap
      {Γ Δ} {ρ : name Γ → name Δ} {M N : affinity}
      (A : species (context.extend N.arity (context.extend M.arity Γ)))
      (A' : species (context.extend M.arity (context.extend N.arity Γ)))
      : subst (name.ext (name.ext ρ)) (subst name.swap A')
      = subst name.swap (subst (name.ext (name.ext ρ)) A')
      := by rw [subst_compose, name.swap.ext_ext, subst_compose]

    /-- Equivalence holds over substitution. -/
    protected theorem subst_pres :
      ∀ {Γ Δ} {A B : species Γ} (ρ : name Γ → name Δ)
      , A ~ B
      → subst ρ A ~ subst ρ B
    | Γ Δ ._ ._ ρ ξ_nil := by { unfold subst, from ξ_nil }
    | Γ Δ ._ ._ ρ (ξ_parallel eq_a eq_b) :=begin
        unfold subst,
        from ξ_parallel (subst_pres ρ eq_a) (subst_pres ρ eq_b)
      end
    | Γ Δ ._ ._ ρ (ξ_restriction M eq) := begin
        unfold subst,
        from ξ_restriction M (subst_pres (name.ext ρ) eq)
      end
    | Γ Δ ._ ._ ρ ξ_choice_nil :=
      by { unfold subst subst.choice, from ξ_choice_nil }
    | Γ Δ ._ ._ ρ (ξ_choice_cons π eq_a eq_as) := sorry

    | Γ Δ ._ ._ ρ (nil_parallel₁ eq) :=
      by { unfold subst, from nil_parallel₁ (subst_pres ρ eq) }
    | Γ Δ ._ ._ ρ (nil_parallel₂ eq) :=
      by { unfold subst, from nil_parallel₂ (subst_pres ρ eq) }

    | Γ Δ ._ ._ ρ (parallel_symm eq_a eq_b) := begin
        unfold subst,
        from parallel_symm (subst_pres ρ eq_a) (subst_pres ρ eq_b)
      end
    | Γ Δ ._ ._ ρ (parallel_assoc₁ eq_a eq_b eq_c) := begin
        unfold subst,
        from parallel_assoc₁ (subst_pres ρ eq_a) (subst_pres ρ eq_b) (subst_pres ρ eq_c)
      end
    | Γ Δ ._ ._ ρ (parallel_assoc₂ eq_a eq_b eq_c) := begin
        unfold subst,
        from parallel_assoc₂ (subst_pres ρ eq_a) (subst_pres ρ eq_b) (subst_pres ρ eq_c)
      end

    | Γ Δ ._ ._ ρ (@ν_parallel₁ _ M A B B' A' eq_a eq_b) := begin
        unfold subst,
        have a : subst (name.ext ρ) A ~ subst name.extend (subst ρ A'),
          rw subst_ext A A', from subst_pres (name.ext ρ) eq_a,
        from ν_parallel₁ M a (subst_pres (name.ext ρ) eq_b)
      end
    | Γ Δ ._ ._ ρ (@ν_parallel₂ _ M A B B' A' eq_a eq_b) := begin
        unfold subst,
        have a : subst (name.ext ρ) A ~ subst name.extend (subst ρ A'),
          rw subst_ext A A', from subst_pres (name.ext ρ) eq_a,
        from ν_parallel₂ M a (subst_pres (name.ext ρ) eq_b)
      end
    | Γ Δ ._ ._ ρ (@ν_drop₁ _ M A A' eq) := begin
        unfold subst,
        have a : subst (name.ext ρ) A ~ subst name.extend (subst ρ A'),
          rw subst_ext A A', from subst_pres (name.ext ρ) eq,
        from ν_drop₁ M a
      end
    | Γ Δ ._ ._ ρ (@ν_drop₂ _ M A A' eq) := begin
        unfold subst,
        have a : subst (name.ext ρ) A ~ subst name.extend (subst ρ A'),
          rw subst_ext A A', from subst_pres (name.ext ρ) eq,
        from ν_drop₂ M a
      end
    | Γ Δ ._ ._ ρ (@ν_swap _ M N A A' eq) := begin
        unfold subst,
        let a : subst (name.ext (name.ext ρ)) A ~ subst name.swap (subst (name.ext (name.ext ρ)) A'),
          rw ← subst_swap A A', from subst_pres (name.ext (name.ext ρ)) eq,
        from ν_swap M N a
      end

    --   /-- Equivalence is symmetric. -/
    --   protected theorem symm : ∀ {Γ} {A B : species Γ}, A ~ B → B ~ A
    --   | Γ ._ ._ ξ_nil := ξ_nil
    --   | Γ ._ ._ (ξ_parallel eq_a eq_b) := ξ_parallel (symm eq_a) (symm eq_b)
    --   | Γ ._ ._ (ξ_restriction M eq) := ξ_restriction M (symm eq)
    --   | Γ ._ ._ ξ_choice_nil := ξ_choice_nil
    --   | Γ ._ ._ (ξ_choice_cons π eq_a eq_as) := ξ_choice_cons π (symm eq_a) (symm eq_as)

    --   | Γ ._ ._ (nil_parallel₁ eq) := nil_parallel₂ eq
    --   | Γ ._ ._ (nil_parallel₂ eq) := nil_parallel₁ eq

    --   | Γ ._ ._ (parallel_symm eq_a eq_b) := parallel_symm (symm eq_b) (symm eq_a)
    --   | Γ ._ ._ (parallel_assoc₁ eq_a eq_b eq_c) := parallel_assoc₂ eq_a eq_b eq_c
    --   | Γ ._ ._ (parallel_assoc₂ eq_a eq_b eq_c) := parallel_assoc₁ eq_a eq_b eq_c

    --   | Γ ._ ._ (ν_parallel₁ M eq_a eq_b) := ν_parallel₂ M eq_a eq_b
    --   | Γ ._ ._ (ν_parallel₂ M eq_a eq_b) := ν_parallel₁ M eq_a eq_b
    --   | Γ ._ ._ (ν_drop₁ M eq_a) := ν_drop₂ M eq_a
    --   | Γ ._ ._ (ν_drop₂ M eq_a) := ν_drop₁ M eq_a
    --   | Γ ._ ._ (@ν_swap _ M N A A' eq) :=
    --       let eq' := symm eq in
    --       let eql :=
    --       calc  subst name.swap (subst name.swap A') ~ subst name.swap A
    --           = subst (name.swap ∘ name.swap) A' ~ subst name.swap A
    --             : by rw subst_compose name.swap name.swap A'
    --       ... = subst id A' ~ subst name.swap A : by rw name.swap.twice_id
    --       ... = A' ~ subst name.swap A : by rw subst_id
    --       in
    --       ν_swap N M (eql ▸ equiv.subst_pres name.swap eq')
    --   using_well_founded {
    --     rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ s, sizeof s.snd )⟩ ],
    --     dec_tac := tactic.fst_dec_tac,
    --   }

    --   -- instance : ∀ {Γ}, is_symm (species Γ) equiv := λ Γ, ⟨ @equiv.symm Γ ⟩

    -- --   -- protected theorem trans : ∀ {A B C : species}, A ~ B → B ~ C → A ~ C
    -- --   -- -- -- We have to unroll each case, as otherwise the totality checker times out.
    -- --   -- -- | nil s2 s3 eq_12 eq_23 :=
    -- --   -- --   match s2, s3, eq_12, eq_23 with
    -- --   -- --   | nil, nil, ξ_nil, ξ_nil := ξ_nil
    -- --   -- --   end
    -- --   -- -- | (_ |ₛ _) s2 s3 eq_12 eq_23 :=
    -- --   -- --   match s2, s3, eq_12, eq_23 with
    -- --   -- --   | _ |ₛ _, _ |ₛ _, ξ_parallel eq_a12 eq_b12, ξ_parallel eq_a23 eq_b23 :=
    -- --   -- --     ξ_parallel (trans eq_a12 eq_a23) (trans eq_b12 eq_b23)
    -- --   -- --   -- | _, _, eq_12, eq_23 with
    -- --   -- --   end
    -- --   -- -- | (ν(_)_) s2 s3 eq_12 eq_23 :=
    -- --   -- --     match s2, s3, eq_12, eq_23 with
    -- --   -- --     | ν(_)_, ν(_)_, ξ_restriction M eq_12, ξ_restriction _ eq_23 :=
    -- --   -- --          ξ_restriction M (trans eq_12 eq_23)
    -- --   -- --     end
    -- --   -- -- | (choice []) s2 s3 eq_12 eq_23 :=
    -- --   -- --   match s2, s3, eq_12, eq_23 with
    -- --   -- --   | choice [], choice [], ξ_choice_nil, ξ_choice_nil := ξ_choice_nil
    -- --   -- --   end
    -- --   -- -- | (choice ((π, A1) :: As)) s2 s3 eq_12 eq_23 :=
    -- --   -- --     match s2, s3, eq_12, eq_23 with
    -- --   -- --     | choice ((_, _)::_), choice ((_, _)::_), ξ_choice_cons _ eq_a12 eq_as12, ξ_choice_cons _ eq_a23 eq_as23 :=
    -- --   -- --       ξ_choice_cons π (trans eq_a12 eq_a23) (trans eq_as12 eq_as23)
    -- --   -- --     end


    -- --   -- -- | nil nil nil ξ_nil ξ_nil := ξ_nil
    -- --   -- -- | (A1 |ₛ B1) (A2 |ₛ B2) (A3 |ₛ B3) (ξ_parallel eq_a12 eq_b12) (ξ_parallel eq_a23 eq_b23) :=
    -- --   -- --     ξ_parallel (trans eq_a12 eq_a23) (trans eq_b12 eq_b23)
    -- --   -- -- | (ν(_)A1) (ν(_)A2) (ν(_)A3) (ξ_restriction M eq_12) (ξ_restriction _ eq_23) :=
    -- --   -- --     ξ_restriction M (trans eq_12 eq_23)
    -- --   -- -- | (choice []) (choice []) (choice[]) ξ_choice_nil ξ_choice_nil := ξ_choice_nil
    -- --   -- -- | (choice ((_, A1)::As1)) (choice ((_, A2)::As2)) (choice ((_, A3)::As3))
    -- --   -- --   (ξ_choice_cons π eq_a12 eq_as12) (ξ_choice_cons _ eq_a23 eq_as23) :=
    -- --   -- --     ξ_choice_cons π (trans eq_a12 eq_a23) (trans eq_as12 eq_as23)
    -- --   -- -- | _ _ _ _ _ := sorry

    -- --   -- | ._ ._ ._ ξ_nil ξ_nil := ξ_nil
    -- --   -- | ._ ._ ._ (ξ_parallel eq_a12 eq_b12) (ξ_parallel eq_a23 eq_b23) :=
    -- --   --     ξ_parallel (trans eq_a12 eq_a23) (trans eq_b12 eq_b23)
    -- --   -- | ._ ._ ._ (ξ_restriction M eq_12) (ξ_restriction _ eq_23) :=
    -- --   --     ξ_restriction M (trans eq_12 eq_23)
    -- --   -- | ._ ._ ._ ξ_choice_nil ξ_choice_nil := ξ_choice_nil
    -- --   -- | ._ ._ ._ (ξ_choice_cons π eq_a12 eq_as12) (ξ_choice_cons _ eq_a23 eq_as23) :=
    -- --   --     ξ_choice_cons π (trans eq_a12 eq_a23) (trans eq_as12 eq_as23)
  end equiv
end species

end cpi
