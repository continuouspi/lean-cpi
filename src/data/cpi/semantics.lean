import data.cpi.basic
import data.cpi.var
import data.cpi.species_equivalence

namespace cpi

inductive concretion : context → ℕ → ℕ → Type
| apply : ∀ {Γ} {b} (bs : vector (name Γ) b) (y : ℕ)
        , species (context.extend y Γ)
        → concretion Γ b y
| parallel₁ : ∀ {Γ} {b y}, concretion Γ b y → species Γ → concretion Γ b y
| parallel₂ : ∀ {Γ} {b y}, species Γ → concretion Γ b y → concretion Γ b y
| restriction : ∀ {Γ} {b y} (M : affinity)
              , concretion (context.extend M.arity Γ) b y
              → concretion Γ b y

notation `#(` b ` ; ` y `)` A := concretion.apply b y A

reserve infixr ` |₁ ` :50
reserve infixr ` |₂ ` :50

infixr ` |₁ ` := concretion.parallel₁
infixr ` |₂ ` := concretion.parallel₂

notation `ν'(` M `) ` A := concretion.restriction M A

namespace concretion
  def subst :
    ∀ {Γ Δ} {b y} (ρ : name Γ → name Δ)
    , concretion Γ b y → concretion Δ b y
  | Γ Δ b y ρ (#(bs; _) A) := #( vector.map ρ bs; y) species.subst (name.ext ρ) A
  | Γ Δ b y ρ (F |₁ A) := subst ρ F |₁ species.subst ρ A
  | Γ Δ b y ρ (A |₂ F) := species.subst ρ A |₂ subst ρ F
  | Γ Δ b y ρ (ν'(M) A) := ν'(M) (subst (name.ext ρ) A)

  theorem subst_compose :
    ∀ {Γ Δ η} {b y} (ρ : name Γ → name Δ) (σ : name Δ → name η) (A : concretion Γ b y)
    , subst σ (subst ρ A) = subst (σ ∘ ρ) A
  | Γ Δ η b ._ ρ σ (#(⟨ elem, n ⟩; y) A) := begin
      unfold subst vector.map,
      rw [species.subst_compose _ _ A, name.ext_comp],
      simp
    end
  | Γ Δ η b y ρ σ (F |₁ A) := begin
      unfold subst,
      rw [subst_compose ρ σ F, species.subst_compose ρ σ A]
    end
  | Γ Δ η b y ρ σ (A |₂ F) := begin
      unfold subst,
      rw [subst_compose ρ σ F, species.subst_compose ρ σ A]
    end
  | Γ Δ η b y ρ σ (ν'(M) A) := begin
      unfold subst,
      rw [subst_compose (name.ext ρ) (name.ext σ) A, name.ext_comp]
    end

  section equivalence
    inductive equiv : ∀ {Γ} {b y}, concretion Γ b y → concretion Γ b y → Prop
    | refl  {Γ} {b y} {F : concretion Γ b y} : equiv F F
    | trans {Γ} {b y} {F G H : concretion Γ b y} : equiv F G → equiv G H → equiv F H
    | symm  {Γ} {b y} {F G : concretion Γ b y} : equiv F G → equiv G F

    | ξ_parallel₁
        {Γ} {b y} {F F' : concretion Γ b y} {A : species Γ}
      : equiv F F' → equiv (F |₁ A) (F' |₁ A)
    | ξ_parallel₂
        {Γ} {b y} {F F' : concretion Γ b y} {A : species Γ}
      : equiv F F' → equiv (F |₁ A) (F' |₁ A)
    | ξ_nu
        {Γ} {b y} (M : affinity) {F F' : concretion (context.extend M.arity Γ) b y}
      : equiv F F' → equiv (ν'(M) F) (ν'(M) F')

    -- Parallel is a commutative monoid
    | parallel_nil
        {Γ} {b y} {F : concretion Γ b y}
      : equiv (F |₁ species.nil) F
    | parallel_symm
        {Γ} {b y} {F : concretion Γ b y} {A : species Γ}
      : equiv (F |₁ A) (A |₂ F)
    | parallel_assoc₁
        {Γ} {b y} {F : concretion Γ b y} {A B : species Γ}
      : equiv ((F |₁ A) |₁ B) (F |₁ (A |ₛ B))
    | parallel_assoc₂
        {Γ} {b y} {F : concretion Γ b y} {A B : species Γ}
      : equiv ((A |₂ F) |₁ B) (A |₂ (F |₁ B))

    -- Projections for species into parallel/apply
    | ξ_parallel
        {Γ} {b y} {F : concretion Γ b y} {A A' : species Γ}
      : A ≈ A' → equiv (F |₁ A) (F |₁ A')
    | ξ_apply
        {Γ} {b y} {bs : vector (name Γ) b} {A A' : species (context.extend y Γ)}
      : A ≈ A' → equiv (#(bs; y) A) (#(bs; y) A')

    -- Standard ν rules
    | ν_parallel₁
        {Γ} {b y} (M : affinity)
        {A : species Γ} {F : concretion (context.extend M.arity Γ) b y}
      : equiv (ν'(M)(species.subst name.extend A |₂ F)) (A |₂ ν'(M) F)
    | ν_parallel₂
        {Γ} {b y} (M : affinity)
        {A : species Γ} {F : concretion (context.extend M.arity Γ) b y}
      : equiv (ν'(M)(F |₁ species.subst name.extend A)) ((ν'(M) F) |₁ A)
    | ν_drop
        {Γ} {b y} (M : affinity) {F : concretion Γ b y}
      : equiv (ν'(M) subst name.extend F) F
    | ν_swap
        {Γ} {b y} (M N : affinity)
        {F : concretion (context.extend N.arity (context.extend M.arity Γ)) b y}
      : equiv (ν'(M)ν'(N) F) (ν'(N)ν'(M) subst name.swap F)

    | apply_parallel
        {Γ} {b y} {bs : vector (name Γ) b}
        {A : species Γ} {B : species (context.extend y Γ)}
      : equiv (#(bs; y) (species.subst name.extend A |ₛ B)) (A |₂ #(bs; y) B)

    local infix ` ⟶ `:51 := equiv

    open equiv

    -- protected def equiv.subst :
    --   ∀ {Γ Δ} {b y} {F G : concretion Γ b y} (ρ : name Γ → name Δ)
    --     , F ⟶ G
    --     → subst ρ F ⟶ subst ρ G
    -- | Γ Δ b y ._ ._ ρ (ξ_parallel₁ eq) :=
    --     by { unfold subst, from ξ_parallel₁ (equiv.subst ρ eq) }
    -- | Γ Δ b y ._ ._ ρ (ξ_parallel₂ eq) :=
    --   by { unfold subst, from ξ_parallel₂ (equiv.subst ρ eq) }
    -- | Γ Δ b y ._ ._ ρ (ξ_nu M eq) :=
    --   by { unfold subst, from ξ_nu M (equiv.subst (name.ext ρ) eq) }
    -- | Γ Δ b y ._ ._ ρ parallel_nil :=
    --   by { unfold subst species.subst has_zero.zero, from parallel_nil }
    -- | Γ Δ b y ._ ._ ρ parallel_symm :=
    --   by { unfold subst, from parallel_symm }
    -- | Γ Δ b y ._ ._ ρ parallel_assoc₁ :=
    --   by { unfold subst species.subst, from parallel_assoc₁ }
    -- | Γ Δ b y ._ ._ ρ parallel_assoc₂ :=
    --   by { unfold subst species.subst, from parallel_assoc₂ }
    -- | Γ Δ b y ._ ._ ρ (ξ_parallel eq) :=
    --     by { unfold subst, from ξ_parallel (species.equiv.subst ρ eq) }
    -- | Γ Δ b y ._ ._ ρ (ξ_apply eq) :=
    --   by { unfold subst, from ξ_apply (species.equiv.subst (name.ext ρ) eq) }
    -- | Γ Δ b y ._ ._ ρ (@ν_parallel₁ _ _ _ M A F) := by {
    --   unfold subst,
    --   rw species.subst_compose,
    --   sorry }
    -- | Γ Δ b y ._ ._ ρ (ν_parallel₂ M) := by { sorry }
    -- | Γ Δ b y ._ ._ ρ (ν_drop M) := by { sorry }
    -- | Γ Δ b y ._ ._ ρ (ν_swap M N) := by { sorry }
    -- | Γ Δ b y ._ ._ ρ apply_parallel := by { sorry }
  end equivalence

  private def depth : ∀ {Γ} {b y}, concretion Γ b y → ℕ
  | _ _ _ (#(_; _) _) := 1
  | _ _ _ (F |₁ _) := depth F + 1
  | _ _ _ (_ |₂ F) := depth F + 1
  | _ _ _ (ν'(M) F) := depth F + 1

  private theorem depth.over_subst :
    ∀ {Γ Δ} {b y} (ρ : name Γ → name Δ) (F : concretion Γ b y)
    , depth F = depth (subst ρ F)
  | Γ Δ b y ρ (#(_; _) _) := by unfold subst depth
  | Γ Δ b y ρ (F |₁ A) := by { unfold subst depth, rw depth.over_subst ρ F }
  | Γ Δ b y ρ (A |₂ F) := by { unfold subst depth, rw depth.over_subst ρ F }
  | Γ Δ b y ρ (ν'(M) F) :=
    by { unfold subst depth, rw depth.over_subst (name.ext ρ) F }

  section pseudo_apply
    private def mk_sub {Γ} {b} (bs : vector (name Γ) b) : name (context.extend b Γ) → name Γ
    | (name.nil idx) := vector.nth bs idx
    | (name.extend e) := e

    /-- Helper function for doign the actual application. This is split up to
        make the totality of pseudo_apply/pseudo_apply_app easier to determine.
    -/
    private def pseudo_apply_app {a b} :
      ∀ {Γ}, vector (name Γ) a → species (context.extend b Γ)
      → concretion Γ b a → species Γ
    | Γ as A (#(bs; y) B) :=
      species.subst (mk_sub bs) A |ₛ species.subst (mk_sub as) B
    | Γ as A (F |₁ B) :=
        pseudo_apply_app as A F |ₛ B
    | Γ as A (B |₂ F) :=
        B |ₛ pseudo_apply_app as A F
    | Γ as A (ν'(M) F) :=
      ν(M) (pseudo_apply_app
             (vector.map name.extend as)
             (species.subst (name.ext name.extend) A)
             F)
    using_well_founded {
      rel_tac := λ _ _,
        `[exact ⟨_, measure_wf (λ x, concretion.sizeof x.fst b a x.snd.snd.snd ) ⟩ ],
      dec_tac := tactic.fst_dec_tac,
    }

    /-- Apply two concretions together. -/
    def pseudo_apply {a b} : ∀ {Γ}, concretion Γ a b → concretion Γ b a → species Γ
    | Γ (#(bs; y) A) F' := pseudo_apply_app bs A F'
    | Γ (F |₁ A) F' := pseudo_apply F F' |ₛ A
    | Γ (A |₂ F) F' := A |ₛ pseudo_apply F F'
    | Γ (ν'(M) F) F' := ν(M) (pseudo_apply F (subst name.extend F'))
    using_well_founded {
      rel_tac := λ _ _,
        `[exact ⟨_, measure_wf (λ x, concretion.sizeof x.fst a b x.snd.fst ) ⟩ ],
      dec_tac := tactic.fst_dec_tac,
    }

    open species.equiv (hiding trans symm refl)

    protected lemma pseudo_apply.on_parallel₁ :
      ∀ {Γ} {a b} (F : concretion Γ a b) (G : concretion Γ b a) (A : species Γ)
      , pseudo_apply F (G |₁ A) ≈ (pseudo_apply F G |ₛ A)
    | Γ a b (#(bs; y) A) G B := by unfold pseudo_apply pseudo_apply_app
    | Γ a b (F |₁ B) G A := begin
        unfold pseudo_apply,
        calc  (pseudo_apply F (G |₁ A) |ₛ B)
            ≈ ((pseudo_apply F G |ₛ A) |ₛ B)
              : ξ_parallel₁ (pseudo_apply.on_parallel₁ F G A)
        ... ≈ ((pseudo_apply F G |ₛ B) |ₛ A) : parallel_symm₂
      end
    | Γ a b (B |₂ F) G A := begin
        unfold pseudo_apply,
        calc  (B |ₛ pseudo_apply F (G |₁ A))
            ≈ (B |ₛ pseudo_apply F G |ₛ A)
              : ξ_parallel₂ (pseudo_apply.on_parallel₁ F G A)
        ... ≈ ((B |ₛ pseudo_apply F G) |ₛ A) : symm parallel_assoc
      end
    | Γ a b (ν'(M) F) G A := begin
        unfold pseudo_apply subst,
        calc  (ν(M) pseudo_apply F (subst name.extend G |₁ species.subst name.extend A))
            ≈ (ν(M) pseudo_apply F (subst name.extend G) |ₛ species.subst name.extend A)
              : ξ_restriction M (pseudo_apply.on_parallel₁ F _ _)
        ... ≈ ((ν(M) pseudo_apply F (subst name.extend G)) |ₛ A) : ν_parallel' M
      end

    protected lemma pseudo_apply.on_parallel₂ :
      ∀ {Γ} {a b} (F : concretion Γ a b) (A : species Γ) (G : concretion Γ b a)
      , pseudo_apply F (A |₂ G) ≈ (A |ₛ pseudo_apply F G)
    | Γ a b (#(bs; y) A) B F := by unfold pseudo_apply pseudo_apply_app
    | Γ a b (F |₁ B) A G := begin
        unfold pseudo_apply,
        calc  (pseudo_apply F (A |₂ G) |ₛ B)
            ≈ ((A |ₛ pseudo_apply F G) |ₛ B)
              : ξ_parallel₁ (pseudo_apply.on_parallel₂ F A G)
        ... ≈ (A |ₛ pseudo_apply F G |ₛ B) : parallel_assoc
      end
    | Γ a b (B |₂ F) A G := begin
        unfold pseudo_apply,
        calc  (B |ₛ pseudo_apply F (A |₂ G))
            ≈ (B |ₛ A |ₛ pseudo_apply F G)
              : ξ_parallel₂ (pseudo_apply.on_parallel₂ F A G)
        ... ≈ (A |ₛ B |ₛ pseudo_apply F G) : parallel_symm₁
      end
    | Γ a b (ν'(M) F) A G := begin
        unfold pseudo_apply subst,
        calc  (ν(M) pseudo_apply F (species.subst name.extend A |₂ subst name.extend G))
            ≈ (ν(M) species.subst name.extend A |ₛ pseudo_apply F (subst name.extend G))
              : ξ_restriction M (pseudo_apply.on_parallel₂ F _ _)
        ... ≈ (A |ₛ ν(M) pseudo_apply F (subst name.extend G)) : ν_parallel M
      end

    private lemma mk_sub.subst
        {Γ Δ} {b} (ρ : name Γ → name Δ) {bs : vector (name Γ) b}
      : ρ ∘ mk_sub bs = mk_sub (vector.map ρ bs) ∘ name.ext ρ := funext $ λ α,
        match α with
        | name.nil idx := by simp [mk_sub, name.ext]
        | name.extend β := by simp only [mk_sub, name.ext, function.comp]
        end

    set_option profiler true
    set_option profiler.threshold 0.5

    -- TODO: Clean up to use calc
    -- TODO: Use induction - does this allow us to drop the explicit termination
    -- checks?

    private lemma pseudo_apply_app.subst {a b} :
      ∀ {Γ Δ} (ρ : name Γ → name Δ)
        (as : vector (name Γ) a) (A : species (context.extend b Γ))
        (F : concretion Γ b a)
      , species.subst ρ (pseudo_apply_app as A F)
      = pseudo_apply_app (vector.map ρ as) (species.subst (name.ext ρ) A) (subst ρ F)
    | Γ Δ ρ as A (#(bs; y) B) := begin
        unfold pseudo_apply_app subst species.subst,
        repeat { rw species.subst_compose },
        repeat { rw mk_sub.subst }
      end
    | Γ Δ ρ bs A (F |₁ B) := begin
        unfold pseudo_apply_app species.subst subst,
        rw pseudo_apply_app.subst ρ bs A F
      end
    | Γ Δ ρ bs A (B |₂ F) := begin
        unfold pseudo_apply_app species.subst subst,
        rw pseudo_apply_app.subst ρ bs A F
      end
    | Γ Δ ρ ⟨ bs, n ⟩ A (ν'(M) G) := begin
        unfold pseudo_apply_app species.subst subst,
        simp,
        have map
          : vector.map (@name.extend _ M.arity) (vector.map ρ ⟨bs, n⟩)
          = vector.map (name.ext ρ) (vector.map name.extend ⟨bs, n⟩),
          unfold vector.map, simp, rw ← name.ext_extend ρ,
        rw map,

        have spc
          : species.subst (name.ext (@name.extend _ M.arity)) (species.subst (name.ext ρ) A)
          = species.subst (name.ext (name.ext ρ)) (species.subst (name.ext name.extend) A),
          rw [species.subst_compose, species.subst_compose],
          rw [name.ext_comp, name.ext_comp],
          rw name.ext_extend ρ,
        rw spc,

        from pseudo_apply_app.subst (name.ext ρ) _ _ G,
      end
    using_well_founded {
      rel_tac := λ _ _,
        `[exact ⟨_, measure_wf (λ x, concretion.sizeof x.fst b a x.snd.snd.snd.snd.snd ) ⟩ ],
      dec_tac := tactic.fst_dec_tac,
    }

    protected lemma pseudo_apply.subst {a b} :
      ∀ {Γ Δ} (ρ : name Γ → name Δ)
        (F : concretion Γ a b) (G : concretion Γ b a)
      , species.subst ρ (pseudo_apply F G) = pseudo_apply (subst ρ F) (subst ρ G)
    | Γ Δ ρ (#(bs; y) A) G := begin
        unfold pseudo_apply subst,
        from pseudo_apply_app.subst ρ bs A G
      end
    | Γ Δ ρ (F |₁ A) G := begin
        unfold pseudo_apply subst species.subst,
        rw pseudo_apply.subst ρ F G
      end
    | Γ Δ ρ (A |₂ F) G := begin
        unfold pseudo_apply subst species.subst,
        rw pseudo_apply.subst ρ F G
      end
    | Γ Δ ρ (ν'(M) F) G := begin
        unfold pseudo_apply subst species.subst,
        -- -- TODO: Clean up to use calc
        rw subst_compose,
        rw ← name.ext_extend,
        rw ← subst_compose name.extend,
        rw pseudo_apply.subst (name.ext ρ) F _,
      end
    using_well_founded {
      rel_tac := λ _ _,
        `[exact ⟨_, measure_wf (λ x, concretion.sizeof x.fst a b x.snd.snd.snd.fst ) ⟩ ],
      dec_tac := tactic.fst_dec_tac,
    }

    protected lemma pseudo_apply.on_restriction :
      ∀ {Γ} {a b} (F : concretion Γ a b) (M : affinity)
        (G : concretion (context.extend M.arity Γ) b a)
      , pseudo_apply F (ν'(M) G) ≈ ν(M) (pseudo_apply (subst name.extend F) G)
    | Γ a b (#(bs; y) A) M G := by unfold pseudo_apply pseudo_apply_app subst
    | Γ a b (F |₁ A) M G := begin
        unfold pseudo_apply subst,
        calc  (pseudo_apply F (ν'(M) G) |ₛ A)
            ≈ ((ν(M) pseudo_apply (subst name.extend F) G) |ₛ A)
              : ξ_parallel₁ (pseudo_apply.on_restriction F M G)
        ... ≈ ν(M) pseudo_apply (subst name.extend F) G |ₛ species.subst name.extend A
              : symm (ν_parallel' M),
      end
    | Γ a b (A |₂ F) M G := begin
        unfold pseudo_apply subst,
        calc  (A |ₛ pseudo_apply F (ν'(M) G))
            ≈ (A |ₛ ν(M) pseudo_apply (subst name.extend F) G)
              : ξ_parallel₂ (pseudo_apply.on_restriction F M G)
        ... ≈ ν(M) species.subst name.extend A |ₛ pseudo_apply (subst name.extend F) G
              : symm (ν_parallel M),
      end
    | Γ a b (ν'(N) F) M G := begin
        unfold pseudo_apply subst,
        calc  (ν(N) pseudo_apply F (ν'(M) subst (name.ext name.extend) G))
            ≈ (ν(N) ν(M) pseudo_apply (subst name.extend F) (subst (name.ext name.extend) G))
              : ξ_restriction N (pseudo_apply.on_restriction F M _)
        ... ≈ (ν(M) ν(N) species.subst name.swap (pseudo_apply (subst name.extend F) (subst (name.ext name.extend) G)))
              : ν_swap N M
        ... ≈ (ν(M) ν(N) (pseudo_apply (subst name.swap (subst name.extend F)) (subst name.swap (subst (name.ext name.extend) G))))
              : by rw pseudo_apply.subst
        ... ≈ (ν(M) ν(N) (pseudo_apply (subst (name.swap ∘ name.extend) F) (subst (name.swap ∘ name.ext name.extend) G)))
              : by rw [subst_compose, subst_compose]
        ... ≈ ν(M) ν(N) pseudo_apply (subst (name.ext name.extend) F) (subst name.extend G)
              : by rw [name.swap.comp_extend, name.swap.comp_ext_extend]
      end

    protected theorem pseudo_apply.symm :
      ∀ {Γ} {a b} (F : concretion Γ a b) (G : concretion Γ b a)
      , pseudo_apply F G ≈ pseudo_apply G F
    | Γ a b (#(as; x) A) (#(bs; y) B) := begin
        unfold pseudo_apply,
        from parallel_symm,
      end
    | Γ a b (#(bs; y) A) (F |₁ B) := begin
        unfold pseudo_apply,
        from ξ_parallel₁ (pseudo_apply.symm (#(bs ; y)A) F),
      end
    | Γ a b (#(bs; y) A) (B |₂ F) := begin
        unfold pseudo_apply,
        from ξ_parallel₂ (pseudo_apply.symm (#(bs ; y)A) F),
      end
    | Γ a b (#(bs; y) A) (ν'(M) F) := begin
        unfold pseudo_apply,
        from ξ_restriction M sorry -- FIXME: (pseudo_apply.symm _ F)
      end

    | Γ a b (F |₁ A) (#(bs; y) B) := begin
        unfold pseudo_apply,
        from ξ_parallel₁ sorry -- FIXME: (pseudo_apply.symm F (#(bs ; y)B)),
      end
    | Γ a b (F |₁ A) (G |₁ B) := begin
        unfold pseudo_apply,
        calc  (pseudo_apply F (G |₁ B) |ₛ A)
            ≈ ((pseudo_apply F G |ₛ B) |ₛ A)
              : ξ_parallel₁ (pseudo_apply.on_parallel₁ F G B)
        ... ≈ ((pseudo_apply G F |ₛ B) |ₛ A)
              : ξ_parallel₁ (ξ_parallel₁ (pseudo_apply.symm F G))
        ... ≈ ((pseudo_apply G F |ₛ A) |ₛ B) : parallel_symm₂
        ... ≈ (pseudo_apply G (F |₁ A) |ₛ B)
              : ξ_parallel₁ (symm (pseudo_apply.on_parallel₁ G F A))
      end
    | Γ a b (F |₁ A) (B |₂ G) := begin
        unfold pseudo_apply,
        calc  (pseudo_apply F (B |₂ G) |ₛ A)
            ≈ ((B |ₛ pseudo_apply F G) |ₛ A)
              : ξ_parallel₁ (pseudo_apply.on_parallel₂ F B G)
        ... ≈ (B |ₛ pseudo_apply F G |ₛ A) : parallel_assoc
        ... ≈ (B |ₛ pseudo_apply G F |ₛ A)
              : ξ_parallel₂ (ξ_parallel₁ (pseudo_apply.symm F G))
        ... ≈ (B |ₛ pseudo_apply G (F |₁ A))
              : ξ_parallel₂ (symm (pseudo_apply.on_parallel₁ G F A))
      end
    | Γ a b (F |₁ A) (restriction M G) := begin
        unfold pseudo_apply subst,
        calc  (pseudo_apply F (ν'(M) G) |ₛ A)
            ≈ ((ν(M) pseudo_apply (subst name.extend F) G) |ₛ A)
              : ξ_parallel₁ (pseudo_apply.on_restriction F M G)
        ... ≈ ((ν(M) pseudo_apply G (subst name.extend F)) |ₛ A)
              : ξ_parallel₁ (ξ_restriction M (pseudo_apply.symm _ G))
        ... ≈ (ν(M) (pseudo_apply G (subst name.extend F)) |ₛ species.subst name.extend A)
              : symm (ν_parallel' M)
        ... ≈ ν(M) pseudo_apply G (subst name.extend F |₁ species.subst name.extend A)
              : ξ_restriction M (symm (pseudo_apply.on_parallel₁ G _ _))
      end

    | Γ a b (A |₂ F) (#(bs; y) G) := begin
        unfold pseudo_apply,
        from ξ_parallel₂ sorry -- FIXME: (pseudo_apply.symm F _),
      end
    | Γ a b (A |₂ F) (G |₁ B) := begin
        unfold pseudo_apply,
        calc  (A |ₛ pseudo_apply F (G |₁ B))
            ≈ (A |ₛ pseudo_apply F G |ₛ B)
              : ξ_parallel₂ (pseudo_apply.on_parallel₁ F G B)
        ... ≈ (A |ₛ pseudo_apply G F |ₛ B)
              : ξ_parallel₂ (ξ_parallel₁ (pseudo_apply.symm _ _))
        ... ≈ ((A |ₛ pseudo_apply G F) |ₛ B) : symm parallel_assoc
        ... ≈ (pseudo_apply G (A |₂ F) |ₛ B)
              : ξ_parallel₁ (symm (pseudo_apply.on_parallel₂ G A F))
      end
    | Γ a b (A |₂ F) (B |₂ G) := begin
        unfold pseudo_apply,
        calc  (A |ₛ pseudo_apply F (B |₂ G))
            ≈ (A |ₛ B |ₛ pseudo_apply F G)
              : ξ_parallel₂ (pseudo_apply.on_parallel₂ F B G)
        ... ≈ (B |ₛ A |ₛ pseudo_apply F G) : parallel_symm₁
        ... ≈ (B |ₛ A |ₛ pseudo_apply G F)
              : ξ_parallel₂ (ξ_parallel₂ (pseudo_apply.symm F G))
        ... ≈ (B |ₛ pseudo_apply G (A |₂ F))
              : ξ_parallel₂ (symm (pseudo_apply.on_parallel₂ G A F))
      end
    | Γ a b (A |₂ F) (ν'(M) G) := begin
        unfold pseudo_apply subst,
        calc  (A |ₛ pseudo_apply F (ν'(M) G))
            ≈ (A |ₛ ν(M) pseudo_apply (subst name.extend F) G)
              : ξ_parallel₂ (pseudo_apply.on_restriction F M G)
        ... ≈ ν(M) species.subst name.extend A |ₛ pseudo_apply (subst name.extend F) G
              : symm (ν_parallel M)
        ... ≈ ν(M) species.subst name.extend A |ₛ pseudo_apply G (subst name.extend F)
              : sorry -- FIXME: ξ_restriction M (ξ_parallel₂ (pseudo_apply.symm _ G))
        ... ≈ ν(M) pseudo_apply G (species.subst name.extend A |₂ subst name.extend F)
              : ξ_restriction M (symm (pseudo_apply.on_parallel₂ G _ _))
    end

    | Γ a b (ν'(M) F) (#(bs; y) G) := begin
        unfold pseudo_apply,
        from ξ_restriction M sorry
      end
    | Γ a b (ν'(M) F) (G |₁ B) := begin
        unfold pseudo_apply,
        calc  (ν(M) pseudo_apply F (subst name.extend (G |₁ B)))
            ≈ (pseudo_apply G (ν'(M) F) |ₛ B) : sorry
      end
    | Γ a b (ν'(M) F) (B |₂ G) := begin
        unfold pseudo_apply,
        calc  (ν(M) pseudo_apply F (subst name.extend (B |₂ G)))
            ≈ (B |ₛ pseudo_apply G (ν'(M) F)) : sorry
      end
    | Γ a b (ν'(M) F) (ν'(N) G) := begin
        unfold pseudo_apply,
        calc  (ν(M) pseudo_apply F (subst name.extend (ν'(N) G)))
            ≈ ν(N) pseudo_apply G (subst name.extend (ν'(M) F))
              : sorry
      end
    -- using_well_founded {
    --   rel_tac := λ _ _,
    --     `[exact ⟨_, measure_wf (λ s, depth s.snd.snd.snd.fst + depth s.snd.snd.snd.snd ) ⟩ ],
    --   dec_tac := do
    --     well_founded_tactics.unfold_wf_rel,
    --     well_founded_tactics.unfold_sizeof,

    --     tactic.dunfold_target [``depth, ``psigma.fst, ``psigma.snd],
    --     well_founded_tactics.cancel_nat_add_lt,
    --     tactic.try well_founded_tactics.trivial_nat_lt
    -- }
  end pseudo_apply

end concretion

end cpi
