import data.cpi.concretion.congruence

namespace cpi
namespace concretion

variables {ℍ : Type} {ω : context}

/-- An alternative measure, simply computes the depth of a term, and thus is
    preserved over renames. -/
private def depth : ∀ {Γ} {b y}, concretion ℍ ω Γ b y → ℕ
| _ _ _ (#(_; _) _) := 1
| _ _ _ (F |₁ _) := depth F + 1
| _ _ _ (_ |₂ F) := depth F + 1
| _ _ _ (ν'(M) F) := depth F + 1

private theorem depth.over_rename :
  ∀ {Γ Δ} {b y} (ρ : name Γ → name Δ) (F : concretion ℍ ω Γ b y)
  , depth F = depth (rename ρ F)
| Γ Δ b y ρ (#(_; _) _) := by unfold rename depth
| Γ Δ b y ρ (F |₁ A) := by { unfold rename depth, rw depth.over_rename ρ F }
| Γ Δ b y ρ (A |₂ F) := by { unfold rename depth, rw depth.over_rename ρ F }
| Γ Δ b y ρ (ν'(M) F) :=
  by { unfold rename depth, rw depth.over_rename (name.ext ρ) F }

/-- Helper function for doign the actual application. This is split up to
    make the totality of pseudo_apply/pseudo_apply_app easier to determine. -/
private def pseudo_apply_app {a b} :
  ∀ {Γ}, vector (name Γ) a → species ℍ ω (context.extend b Γ)
  → concretion ℍ ω Γ b a → species ℍ ω Γ
| Γ as A (#(bs; y) B) :=
  species.rename (name.mk_apply bs) A |ₛ species.rename (name.mk_apply as) B
| Γ as A (F |₁ B) :=
    pseudo_apply_app as A F |ₛ B
| Γ as A (B |₂ F) :=
    B |ₛ pseudo_apply_app as A F
| Γ as A (ν'(M) F) :=
  ν(M) (pseudo_apply_app
          (vector.map name.extend as)
          (species.rename (name.ext name.extend) A)
          F)
using_well_founded {
  rel_tac := λ _ _,
    `[exact ⟨_, measure_wf (λ x, concretion.sizeof ℍ ω x.fst b a x.snd.snd.snd ) ⟩ ],
  dec_tac := tactic.fst_dec_tac,
}

/-- Apply two concretions together. -/
def pseudo_apply {a b} : ∀ {Γ}, concretion ℍ ω Γ a b → concretion ℍ ω Γ b a → species ℍ ω Γ
| Γ (#(bs; y) A) F' := pseudo_apply_app bs A F'
| Γ (F |₁ A) F' := pseudo_apply F F' |ₛ A
| Γ (A |₂ F) F' := A |ₛ pseudo_apply F F'
| Γ (ν'(M) F) F' := ν(M) (pseudo_apply F (rename name.extend F'))
using_well_founded {
  rel_tac := λ _ _,
    `[exact ⟨_, measure_wf (λ x, concretion.sizeof ℍ ω x.fst a b x.snd.fst ) ⟩ ],
  dec_tac := tactic.fst_dec_tac,
}

open species.equiv (hiding trans symm refl)
open_locale congruence

protected lemma pseudo_apply.on_parallel₁ :
  ∀ {Γ} {a b} (F : concretion ℍ ω Γ a b) (G : concretion ℍ ω Γ b a) (A : species ℍ ω Γ)
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
    ... ≈ ((B |ₛ pseudo_apply F G) |ₛ A) : parallel_assoc₂
  end
| Γ a b (ν'(M) F) G A := begin
    unfold pseudo_apply rename,
    calc  (ν(M) pseudo_apply F (rename name.extend G |₁ species.rename name.extend A))
        ≈ (ν(M) pseudo_apply F (rename name.extend G) |ₛ species.rename name.extend A)
          : ξ_restriction M (pseudo_apply.on_parallel₁ F _ _)
    ... ≈ ((ν(M) pseudo_apply F (rename name.extend G)) |ₛ A) : ν_parallel' M
  end

protected lemma pseudo_apply.on_parallel₂ :
  ∀ {Γ} {a b} (F : concretion ℍ ω Γ a b) (A : species ℍ ω Γ) (G : concretion ℍ ω Γ b a)
  , pseudo_apply F (A |₂ G) ≈ (A |ₛ pseudo_apply F G)
| Γ a b (#(bs; y) A) B F := by unfold pseudo_apply pseudo_apply_app
| Γ a b (F |₁ B) A G := begin
    unfold pseudo_apply,
    calc  (pseudo_apply F (A |₂ G) |ₛ B)
        ≈ ((A |ₛ pseudo_apply F G) |ₛ B)
          : ξ_parallel₁ (pseudo_apply.on_parallel₂ F A G)
    ... ≈ (A |ₛ pseudo_apply F G |ₛ B) : parallel_assoc₁
  end
| Γ a b (B |₂ F) A G := begin
    unfold pseudo_apply,
    calc  (B |ₛ pseudo_apply F (A |₂ G))
        ≈ (B |ₛ A |ₛ pseudo_apply F G)
          : ξ_parallel₂ (pseudo_apply.on_parallel₂ F A G)
    ... ≈ (A |ₛ B |ₛ pseudo_apply F G) : parallel_symm₁
  end
| Γ a b (ν'(M) F) A G := begin
    unfold pseudo_apply rename,
    calc  (ν(M) pseudo_apply F (species.rename name.extend A |₂ rename name.extend G))
        ≈ (ν(M) species.rename name.extend A |ₛ pseudo_apply F (rename name.extend G))
          : ξ_restriction M (pseudo_apply.on_parallel₂ F _ _)
    ... ≈ (A |ₛ ν(M) pseudo_apply F (rename name.extend G)) : ν_parallel₁ M
  end

-- TODO: Clean up to use calc
-- TODO: Use induction - does this allow us to drop the explicit termination
-- checks?

private lemma pseudo_apply_app.rename {a b} :
  ∀ {Γ Δ} (ρ : name Γ → name Δ)
    (as : vector (name Γ) a) (A : species ℍ ω (context.extend b Γ))
    (F : concretion ℍ ω Γ b a)
  , species.rename ρ (pseudo_apply_app as A F)
  = pseudo_apply_app (vector.map ρ as) (species.rename (name.ext ρ) A) (rename ρ F)
| Γ Δ ρ as A (#(bs; y) B) := begin
    unfold pseudo_apply_app rename,
    simp [species.rename_compose, name.mk_apply_rename]
  end
| Γ Δ ρ bs A (F |₁ B) := begin
    unfold pseudo_apply_app rename,
    simp [pseudo_apply_app.rename ρ bs A F]
  end
| Γ Δ ρ bs A (B |₂ F) := begin
    unfold pseudo_apply_app rename,
    simp [pseudo_apply_app.rename ρ bs A F]
  end
| Γ Δ ρ ⟨ bs, n ⟩ A (ν'(M) G) := begin
    unfold pseudo_apply_app rename,
    simp,
    have map
      : vector.map (@name.extend _ M.arity) (vector.map ρ ⟨bs, n⟩)
      = vector.map (name.ext ρ) (vector.map name.extend ⟨bs, n⟩),
      unfold vector.map, simp, rw ← name.ext_extend ρ,
    rw map,

    have spc
      : species.rename (name.ext (@name.extend _ M.arity)) (species.rename (name.ext ρ) A)
      = species.rename (name.ext (name.ext ρ)) (species.rename (name.ext name.extend) A),
      rw [species.rename_compose, species.rename_compose],
      rw [name.ext_comp, name.ext_comp],
      rw name.ext_extend ρ,
    rw spc,

    from pseudo_apply_app.rename (name.ext ρ) _ _ G,
  end
using_well_founded {
  rel_tac := λ _ _,
    `[exact ⟨_, measure_wf (λ x, concretion.sizeof ℍ ω x.fst b a x.snd.snd.snd.snd.snd ) ⟩ ],
  dec_tac := tactic.fst_dec_tac,
}

protected lemma pseudo_apply.rename {a b} :
  ∀ {Γ Δ} (ρ : name Γ → name Δ)
    (F : concretion ℍ ω Γ a b) (G : concretion ℍ ω Γ b a)
  , species.rename ρ (pseudo_apply F G) = pseudo_apply (rename ρ F) (rename ρ G)
| Γ Δ ρ (#(bs; y) A) G := begin
    unfold pseudo_apply rename,
    from pseudo_apply_app.rename ρ bs A G
  end
| Γ Δ ρ (F |₁ A) G := begin
    unfold pseudo_apply rename,
    simp [pseudo_apply.rename ρ F G]
  end
| Γ Δ ρ (A |₂ F) G := begin
    unfold pseudo_apply rename,
    simp [pseudo_apply.rename ρ F G]
  end
| Γ Δ ρ (ν'(M) F) G := begin
    unfold pseudo_apply rename, simp,
    -- -- TODO: Clean up to use calc
    rw rename_compose,
    rw ← name.ext_extend,
    rw ← rename_compose name.extend,
    rw pseudo_apply.rename (name.ext ρ) F _,
  end
using_well_founded {
  rel_tac := λ _ _,
    `[exact ⟨_, measure_wf (λ x, concretion.sizeof ℍ ω x.fst a b x.snd.snd.snd.fst ) ⟩ ],
  dec_tac := tactic.fst_dec_tac,
}

private lemma pseudo_apply.restriction_swap {a b}:
  ∀ {Γ} (M N : affinity ℍ)
    (F : concretion ℍ ω (context.extend N.arity Γ) a b)
    (G : concretion ℍ ω (context.extend M.arity Γ) b a)
  , (ν(N) ν(M) pseudo_apply (rename name.extend F) (rename (name.ext name.extend) G))
  ≈ ν(M) ν(N) pseudo_apply (rename (name.ext name.extend) F) (rename name.extend G)
| Γ M N F G :=
    calc  (ν(N) ν(M) pseudo_apply (rename name.extend F) (rename (name.ext name.extend) G))
        ≈ (ν(M) ν(N) species.rename name.swap (pseudo_apply (rename name.extend F) (rename (name.ext name.extend) G)))
          : ν_swap₁ N M
    ... ≈ (ν(M) ν(N) (pseudo_apply (rename name.swap (rename name.extend F)) (rename name.swap (rename (name.ext name.extend) G))))
          : by rw pseudo_apply.rename
    ... ≈ (ν(M) ν(N) (pseudo_apply (rename (name.swap ∘ name.extend) F) (rename (name.swap ∘ name.ext name.extend) G)))
          : by rw [rename_compose, rename_compose]
    ... ≈ ν(M) ν(N) pseudo_apply (rename (name.ext name.extend) F) (rename name.extend G)
          : by rw [name.swap_comp_extend, name.swap_comp_ext_extend]

lemma pseudo_apply.on_restriction :
  ∀ {Γ} {a b} (F : concretion ℍ ω Γ a b) (M : affinity ℍ)
    (G : concretion ℍ ω (context.extend M.arity Γ) b a)
  , pseudo_apply F (ν'(M) G) ≈ ν(M) (pseudo_apply (rename name.extend F) G)
| Γ a b (#(bs; y) A) M G := by unfold pseudo_apply pseudo_apply_app rename
| Γ a b (F |₁ A) M G := begin
    unfold pseudo_apply rename,
    calc  (pseudo_apply F (ν'(M) G) |ₛ A)
        ≈ ((ν(M) pseudo_apply (rename name.extend F) G) |ₛ A)
          : ξ_parallel₁ (pseudo_apply.on_restriction F M G)
    ... ≈ ν(M) pseudo_apply (rename name.extend F) G |ₛ species.rename name.extend A
          : symm (ν_parallel' M),
  end
| Γ a b (A |₂ F) M G := begin
    unfold pseudo_apply rename,
    calc  (A |ₛ pseudo_apply F (ν'(M) G))
        ≈ (A |ₛ ν(M) pseudo_apply (rename name.extend F) G)
          : ξ_parallel₂ (pseudo_apply.on_restriction F M G)
    ... ≈ ν(M) species.rename name.extend A |ₛ pseudo_apply (rename name.extend F) G
          : ν_parallel₂ M,
  end
| Γ a b (ν'(N) F) M G := begin
    unfold pseudo_apply rename,
    calc  (ν(N) pseudo_apply F (ν'(M) rename (name.ext name.extend) G))
        ≈ (ν(N) ν(M) pseudo_apply (rename name.extend F) (rename (name.ext name.extend) G))
          : ξ_restriction N (pseudo_apply.on_restriction F M _)
    ... ≈ ν(M) ν(N) pseudo_apply (rename (name.ext name.extend) F) (rename name.extend G)
          : pseudo_apply.restriction_swap M N F G
  end

private theorem pseudo_apply_app.symm {a b} :
  ∀ {Γ} (bs : vector (name Γ) a) (A : species ℍ ω (context.extend b Γ))
    (G : concretion ℍ ω Γ b a)
  , pseudo_apply_app bs A G ≈ pseudo_apply G (#(bs; b) A) := begin
  intros Γ as A G,
  induction G,

  case apply : Γ' b' bs y A {
    unfold pseudo_apply pseudo_apply_app,
    from parallel_symm
  },

  case parallel₁ : Γ' b' y F A ih {
      unfold pseudo_apply pseudo_apply_app,
      from ξ_parallel₁ (ih _ _)
  },

  case parallel₂ : Γ' b' y A F ih {
      unfold pseudo_apply pseudo_apply_app,
      from ξ_parallel₂ (ih _ _)
  },

  case restriction : Γ' b' y M F ih {
    unfold pseudo_apply pseudo_apply_app,
    from ξ_restriction M (ih _ _)
  }
end

theorem pseudo_apply.symm {a b} :
  ∀ {Γ} (F : concretion ℍ ω Γ a b) (G : concretion ℍ ω Γ b a)
  , pseudo_apply F G ≈ pseudo_apply G F
| Γ (#(as; x) A) G := begin
    unfold pseudo_apply,
    from pseudo_apply_app.symm as A G
  end

| Γ (F |₁ A) (#(bs; y) B) := begin
    unfold pseudo_apply pseudo_apply_app,
    from ξ_parallel₁ (symm (pseudo_apply_app.symm bs B F)),
  end
| Γ (F |₁ A) (G |₁ B) := begin
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
| Γ (F |₁ A) (B |₂ G) := begin
    unfold pseudo_apply,
    calc  (pseudo_apply F (B |₂ G) |ₛ A)
        ≈ ((B |ₛ pseudo_apply F G) |ₛ A)
          : ξ_parallel₁ (pseudo_apply.on_parallel₂ F B G)
    ... ≈ (B |ₛ pseudo_apply F G |ₛ A) : parallel_assoc₁
    ... ≈ (B |ₛ pseudo_apply G F |ₛ A)
          : ξ_parallel₂ (ξ_parallel₁ (pseudo_apply.symm F G))
    ... ≈ (B |ₛ pseudo_apply G (F |₁ A))
          : ξ_parallel₂ (symm (pseudo_apply.on_parallel₁ G F A))
  end
| Γ (F |₁ A) (ν'(M) G) := begin
    unfold pseudo_apply rename,
    calc  (pseudo_apply F (ν'(M) G) |ₛ A)
        ≈ ((ν(M) pseudo_apply (rename name.extend F) G) |ₛ A)
          : ξ_parallel₁ (pseudo_apply.on_restriction F M G)
    ... ≈ ((ν(M) pseudo_apply G (rename name.extend F)) |ₛ A)
          : ξ_parallel₁ (ξ_restriction M (pseudo_apply.symm _ G))
    ... ≈ (ν(M) (pseudo_apply G (rename name.extend F)) |ₛ species.rename name.extend A)
          : symm (ν_parallel' M)
    ... ≈ ν(M) pseudo_apply G (rename name.extend F |₁ species.rename name.extend A)
          : ξ_restriction M (symm (pseudo_apply.on_parallel₁ G _ _))
  end

| Γ (A |₂ F) (#(bs; y) B) := begin
    unfold pseudo_apply pseudo_apply_app,
    from ξ_parallel₂ (symm (pseudo_apply_app.symm bs B F)),
  end
| Γ (A |₂ F) (G |₁ B) := begin
    unfold pseudo_apply,
    calc  (A |ₛ pseudo_apply F (G |₁ B))
        ≈ (A |ₛ pseudo_apply F G |ₛ B)
          : ξ_parallel₂ (pseudo_apply.on_parallel₁ F G B)
    ... ≈ (A |ₛ pseudo_apply G F |ₛ B)
          : ξ_parallel₂ (ξ_parallel₁ (pseudo_apply.symm F G))
    ... ≈ ((A |ₛ pseudo_apply G F) |ₛ B) : parallel_assoc₂
    ... ≈ (pseudo_apply G (A |₂ F) |ₛ B)
          : ξ_parallel₁ (symm (pseudo_apply.on_parallel₂ G A F))
  end
| Γ (A |₂ F) (B |₂ G) := begin
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
| Γ (A |₂ F) (ν'(M) G) := begin
    unfold pseudo_apply rename,
    calc  (A |ₛ pseudo_apply F (ν'(M) G))
        ≈ (A |ₛ ν(M) pseudo_apply (rename name.extend F) G)
          : ξ_parallel₂ (pseudo_apply.on_restriction F M G)
    ... ≈ ν(M) species.rename name.extend A |ₛ pseudo_apply (rename name.extend F) G
          : ν_parallel₂ M
    ... ≈ ν(M) species.rename name.extend A |ₛ pseudo_apply G (rename name.extend F)
          : ξ_restriction M (ξ_parallel₂ (pseudo_apply.symm _ G))
    ... ≈ ν(M) pseudo_apply G (species.rename name.extend A |₂ rename name.extend F)
          : ξ_restriction M (symm (pseudo_apply.on_parallel₂ G _ _))
end

| Γ (ν'(M) F) (#(bs; y) B) := begin
    unfold pseudo_apply pseudo_apply_app,
    from ξ_restriction M (symm (pseudo_apply_app.symm _ _ F)),
  end
| Γ (ν'(M) F) (G |₁ B) :=
  let h : depth (rename (@name.extend Γ M.arity) G) < depth G + 1 := begin
    rw ← depth.over_rename name.extend G,
    from nat.lt_add_of_pos_right nat.zero_lt_one
  end in begin
    unfold pseudo_apply rename,
    calc  (ν(M) pseudo_apply F (rename name.extend G |₁ species.rename name.extend B))
        ≈ (ν(M) pseudo_apply F (rename name.extend G) |ₛ species.rename name.extend B)
          : ξ_restriction M (pseudo_apply.on_parallel₁ F _ _)
    ... ≈ ((ν(M) pseudo_apply F (rename name.extend G)) |ₛ B) : ν_parallel' M
    ... ≈ ((ν(M) pseudo_apply (rename name.extend G) F) |ₛ B)
          : ξ_parallel₁ (ξ_restriction M (pseudo_apply.symm F (rename name.extend G)))
    ... ≈ (pseudo_apply G (ν'(M) F) |ₛ B)
          : ξ_parallel₁ (symm (pseudo_apply.on_restriction G M F))
  end
| Γ (ν'(M) F) (B |₂ G) :=
  let h : depth (rename (@name.extend Γ M.arity) G) < depth G + 1 := begin
    rw ← depth.over_rename name.extend G,
    from nat.lt_add_of_pos_right nat.zero_lt_one
  end in begin
    unfold pseudo_apply rename,
    calc  (ν(M) pseudo_apply F (species.rename name.extend B |₂ rename name.extend G))
        ≈ (ν(M) species.rename name.extend B |ₛ pseudo_apply F (rename name.extend G))
          : ξ_restriction M (pseudo_apply.on_parallel₂ F _ _)
    ... ≈ (B |ₛ ν(M) pseudo_apply F (rename name.extend G)) : ν_parallel₁ M
    ... ≈ (B |ₛ ν(M) pseudo_apply (rename name.extend G) F)
          : ξ_parallel₂ (ξ_restriction M (pseudo_apply.symm F _))
    ... ≈ (B |ₛ pseudo_apply G (ν'(M) F))
          : ξ_parallel₂ (symm (pseudo_apply.on_restriction G M F))
  end
| Γ (ν'(M) F) (ν'(N) G) :=
  let h : depth (rename (name.ext (@name.extend Γ M.arity)) G) < depth G + 1 := begin
    rw ← depth.over_rename _ G,
    from nat.lt_add_of_pos_right nat.zero_lt_one
  end in begin
    unfold pseudo_apply rename,
    calc  (ν(M) pseudo_apply F (ν'(N) rename (name.ext name.extend) G))
        ≈ (ν(M) ν(N) pseudo_apply (rename name.extend F) (rename (name.ext name.extend) G))
          : ξ_restriction M (pseudo_apply.on_restriction F N _)
    ... ≈ (ν(M) ν(N) pseudo_apply (rename (name.ext name.extend) G) (rename name.extend F))
          : ξ_restriction M (ξ_restriction N (pseudo_apply.symm _ _))
    ... ≈ ν(N) ν(M) pseudo_apply (rename name.extend G) (rename (name.ext name.extend) F)
          : symm (pseudo_apply.restriction_swap M N G F)
    ... ≈ ν(N) pseudo_apply G (ν'(M) rename (name.ext name.extend) F)
          : ξ_restriction N (symm (pseudo_apply.on_restriction G M _))
  end
using_well_founded {
  rel_tac := λ _ _,
    `[exact ⟨_, measure_wf (λ x, depth x.snd.snd ) ⟩ ],
  dec_tac := do
    well_founded_tactics.unfold_wf_rel,
    well_founded_tactics.unfold_sizeof,

    tactic.dunfold_target [``depth, ``psigma.fst, ``psigma.snd],
    well_founded_tactics.cancel_nat_add_lt,
    tactic.try well_founded_tactics.trivial_nat_lt
}

private lemma pseudo_apply_app.equiv {a b} :
  ∀ {Γ} {bs : vector (name Γ) a} {A A' : species ℍ ω (context.extend b Γ)}
    {F : concretion ℍ ω Γ b a}
  , A ≈ A' → pseudo_apply_app bs A F ≈ pseudo_apply_app bs A' F :=
begin
  intros Γ as A A' G eq,
  induction G,

  case apply : Γ b bs y B {
    unfold pseudo_apply_app,
    from ξ_parallel₁ (species.equiv.rename _ eq),
  },
  case parallel₁ : Γ b y F B ih {
    unfold pseudo_apply_app,
    from ξ_parallel₁ (ih eq)
  },
  case parallel₂ : Γ b y B F ih {
    unfold pseudo_apply_app,
    from ξ_parallel₂ (ih eq)
  },
  case restriction : Γ b y M F ih {
    unfold pseudo_apply_app,
    from ξ_restriction M (ih (species.equiv.rename _ eq)),
  }
end

private lemma pseudo_apply_app.par {a b} :
  ∀ {Γ} (bs : vector (name Γ) a)
    (A : species ℍ ω Γ) (B : species ℍ ω (context.extend b Γ))
    (G : concretion ℍ ω Γ b a)
  , pseudo_apply_app bs (species.rename name.extend A |ₛ B) G ≈ (A |ₛ pseudo_apply_app bs B G) :=
begin
  intros Γ as A B G,
  induction G,

  case apply : _ b' bs y C {
    unfold pseudo_apply_app, simp,
    calc  ((species.rename (name.mk_apply bs) (species.rename name.extend A) |ₛ species.rename (name.mk_apply bs) B)
            |ₛ species.rename (name.mk_apply as) C)
        ≈ ((species.rename (name.mk_apply bs ∘ name.extend) A |ₛ species.rename (name.mk_apply bs) B)
            |ₛ species.rename (name.mk_apply as) C)
          : by rw species.rename_compose _ _ A
    ... ≈ ((A |ₛ species.rename (name.mk_apply bs) B) |ₛ species.rename (name.mk_apply as) C)
          : by { rw [name.mk_apply_ext, species.rename_id], }
    ... ≈ (A |ₛ species.rename (name.mk_apply bs) B |ₛ species.rename (name.mk_apply as) C)
          : parallel_assoc₁
  },

  case parallel₁ : _ b' y G C ih {
    unfold pseudo_apply_app species.rename,
    calc  (pseudo_apply_app as (species.rename name.extend A |ₛ B) G |ₛ C)
        ≈ ((A |ₛ pseudo_apply_app as B G) |ₛ C) : ξ_parallel₁ (ih as A B)
    ... ≈ (A |ₛ pseudo_apply_app as B G |ₛ C) : parallel_assoc₁
  },

  case parallel₂ : _ b' y C G ih {
    unfold pseudo_apply_app species.rename,
    calc  (C |ₛ pseudo_apply_app as (species.rename name.extend A |ₛ B) G)
        ≈ (C |ₛ (A |ₛ pseudo_apply_app as B G)) : ξ_parallel₂ (ih as A B)
    ... ≈ (A |ₛ C |ₛ pseudo_apply_app as B G) : parallel_symm₁
  },

  case restriction : _ b' y' M G ih {
    unfold pseudo_apply_app, simp,
    calc  (ν(M) pseudo_apply_app (vector.map name.extend as)
                  (species.rename (name.ext name.extend) (species.rename name.extend A)
                  |ₛ species.rename (name.ext name.extend) B) G)
        ≈ (ν(M) pseudo_apply_app (vector.map name.extend as)
                  (species.rename name.extend (species.rename name.extend A)
                  |ₛ species.rename (name.ext name.extend) B) G)
          : by rw ← species.rename_ext A
    ... ≈ (ν(M) species.rename name.extend A |ₛ
                pseudo_apply_app (vector.map name.extend as)
                    (species.rename (name.ext name.extend) B) G)
          : ξ_restriction M (ih _ _ _)
    ... ≈ (A |ₛ ν(M)
                pseudo_apply_app (vector.map name.extend as)
                    (species.rename (name.ext name.extend) B) G)
        : ν_parallel₁ M
  }
end

lemma pseudo_apply.equiv_l {a b} :
  ∀ {Γ} {F F' : concretion ℍ ω Γ a b} {G : concretion ℍ ω Γ b a}
  , F ≈ F' → pseudo_apply F G ≈ pseudo_apply F' G :=
begin
  intros Γ F F' G eq, induction eq,

  -- Modifiers are incredibly trivial
  case equiv.refl { from refl _ },
  case equiv.trans : Γ b y F G H fg gh ih_fg ih_gh { from trans ih_fg ih_gh },
  case equiv.symm : Γ b y F G eq ih_eq { from symm ih_eq },

  -- Projections are trivial
  case equiv.ξ_parallel₁ : Γ b y F F' A eq ih {
    unfold pseudo_apply,
    from ξ_parallel₁ ih
  },
  case equiv.ξ_parallel₂ : Γ b y A F F' eq ih {
    unfold pseudo_apply,
    from ξ_parallel₂ ih
  },
  case equiv.ξ_restriction : Γ b y M F F' eq ih {
    unfold pseudo_apply,
    from ξ_restriction M ih
  },

  -- Now for the interesting stuff. Well, relatively speaking.

  case equiv.parallel_nil : Γ b y F { unfold pseudo_apply, from parallel_nil₁ },
  case equiv.parallel_symm : Γ b y F G { unfold pseudo_apply, from parallel_symm },
  case equiv.parallel_assoc₁ : Γ b y F A B {
    unfold pseudo_apply,
    from parallel_assoc₁
  },
  case equiv.parallel_assoc₂ : Γ b y F A B {
    unfold pseudo_apply,
    from parallel_assoc₁
  },

  case equiv.ξ_apply : Γ b y bs A A' eq F {
    unfold pseudo_apply,
    from pseudo_apply_app.equiv eq
  },
  case equiv.ξ_parallel : Γ b y F A A' eq {
    unfold pseudo_apply,
    from ξ_parallel₂ eq
  },

  case equiv.ν_parallel₁ : Γ b y M A F {
    unfold pseudo_apply,
    from ν_parallel₁ M
  },
  case equiv.ν_parallel₂ : Γ b y M F F {
    unfold pseudo_apply,
    rw ← pseudo_apply.rename name.extend F G,
    from ν_parallel₁ M
  },
  case equiv.ν_drop : Γ b y M F {
    unfold pseudo_apply,
    rw ← pseudo_apply.rename name.extend F G,
    from ν_drop₁ M
  },
  case equiv.ν_swap : Γ b y M N F {
    unfold pseudo_apply,
    calc  (ν(M) ν(N) pseudo_apply F (rename name.extend (rename name.extend G)))
        ≈ (ν(M) ν(N) pseudo_apply F (rename (name.extend ∘ name.extend) G))
          : by rw rename_compose
    ... ≈ (ν(N) ν(M) pseudo_apply (rename name.swap F) (rename name.swap (rename (name.extend ∘ name.extend) G)))
          : by { rw ← pseudo_apply.rename, from ν_swap₁ M N }
    ... ≈ (ν(N) ν(M) pseudo_apply (rename name.swap F) (rename (name.swap ∘ name.extend ∘ name.extend) G))
          : by rw rename_compose
    ... ≈ (ν(N) ν(M) pseudo_apply (rename name.swap F) (rename (name.extend ∘ name.extend) G))
          : by rw [← function.comp.assoc, name.swap_comp_extend, name.ext_extend]
    ... ≈ (ν(N) ν(M) pseudo_apply (rename name.swap F) (rename name.extend (rename name.extend G)))
          : by rw rename_compose
  },
  case equiv.apply_parallel : Γ b y bs A B {
    unfold pseudo_apply,
    from pseudo_apply_app.par bs A B G
  }
end

theorem pseudo_apply.equiv {a b} :
  ∀ {Γ} {F F' : concretion ℍ ω Γ a b} {G G' : concretion ℍ ω Γ b a}
  , F ≈ F' → G ≈ G' → pseudo_apply F G ≈ pseudo_apply F' G'
| Γ F F' G G' eq_1 eq_2 :=
  calc  pseudo_apply F  G
      ≈ pseudo_apply F' G  : pseudo_apply.equiv_l eq_1
  ... ≈ pseudo_apply G  F' : pseudo_apply.symm F' G
  ... ≈ pseudo_apply G' F' : pseudo_apply.equiv_l eq_2
  ... ≈ pseudo_apply F' G' : pseudo_apply.symm G' F'

protected lemma pseudo_apply.on_parallel₂'
    {Γ} {a b} (A : species ℍ ω Γ) (F : concretion ℍ ω Γ a b) (G : concretion ℍ ω Γ b a)
  : pseudo_apply (A |₂ F) G ≈ (A |ₛ pseudo_apply F G) :=
  calc  pseudo_apply (A |₂ F) G
      ≈ pseudo_apply G (A |₂ F) : pseudo_apply.symm _ G
  ... ≈ (A |ₛ pseudo_apply G F) : pseudo_apply.on_parallel₂ G A F
  ... ≈ (A |ₛ pseudo_apply F G) : ξ_parallel₂ (pseudo_apply.symm G F)

protected lemma pseudo_apply.parallel_shift
    {Γ} {a b} (F : concretion ℍ ω Γ a b) (A : species ℍ ω Γ) (G : concretion ℍ ω Γ b a)
  : pseudo_apply (F |₁ A) G ≈ pseudo_apply F (A |₂ G) :=
  calc  pseudo_apply (F |₁ A) G
      ≈ pseudo_apply G (F |₁ A) : pseudo_apply.symm _ G
  ... ≈ (pseudo_apply G F |ₛ A) : pseudo_apply.on_parallel₁ G F A
  ... ≈ (A |ₛ pseudo_apply G F) : parallel_symm
  ... ≈ (A |ₛ pseudo_apply F G) : ξ_parallel₂ (pseudo_apply.symm G F)
  ... ≈ pseudo_apply F (A |₂ G) : symm (pseudo_apply.on_parallel₂ F A G)

/-- Pseudo application lifted to the level of quotients. -/
def pseudo_apply.quotient {Γ a b}
  : concretion' ℍ ω Γ a b → concretion' ℍ ω Γ b a
  → species' ℍ ω Γ
| F G := quotient.lift_on₂ F G
  (λ F G, ⟦ pseudo_apply F G ⟧)
  (λ F G F' G' eqF eqG, quot.sound (pseudo_apply.equiv eqF eqG))

lemma pseudo_apply.quotient.symm {Γ a b} :
  ∀ (F : concretion' ℍ ω Γ a b) (G : concretion' ℍ ω Γ b a)
  , pseudo_apply.quotient F G = pseudo_apply.quotient G F
| F G := begin
  rcases quot.exists_rep F with ⟨ F, ⟨ _ ⟩ ⟩,
  rcases quot.exists_rep G with ⟨ G, ⟨ _ ⟩ ⟩,

  show ⟦pseudo_apply F G⟧ = ⟦pseudo_apply G F⟧,
  from quot.sound (pseudo_apply.symm F G),
end

end concretion
end cpi

#lint-
