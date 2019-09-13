import data.cpi.basic
import data.cpi.var

namespace cpi

inductive concretion : context → ℕ → ℕ → Type
| apply : ∀ {Γ} {b} (bs : vector (name Γ) b) (y : ℕ)
        , species (context.extend y Γ)
        → concretion Γ b y
| parallel₁ : ∀ {Γ} {b y}, concretion Γ b y → species Γ → concretion Γ b y
| parallel₂ : ∀ {Γ} {b y}, species Γ → concretion Γ b y → concretion Γ b y
| restriction : ∀{Γ} {b y} (M : affinity)
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

  -- set_option pp.implicit true

  def pseudo_apply : ∀ {Γ} {a b}, concretion Γ a b → concretion Γ b a → species Γ
  | Γ a b (#(as; x) A) (#(bs; y) B) := sorry
  | Γ a b (#(as; x) A) (F |₁ B) :=
      pseudo_apply (#(as; x) A) F |ₛ B
  | Γ a b (#(as; x) A) (B |₂ F) :=
      B |ₛ pseudo_apply (#(as; x) A) F
  | Γ a b (#(as; x) A) (ν'(M) F) := sorry

  | Γ a b (parallel₁ F A) F' := pseudo_apply F F' |ₛ A
  | Γ a b (parallel₂ A F) F' := A |ₛ pseudo_apply F F'
  | Γ a b (ν'(M) F) F' :=
    -- Used for termination checking
    have h : depth (subst (@name.extend Γ M.arity) F') < 1 + depth F' := begin
      rw ← depth.over_subst name.extend F',
      simp only [lt_add_iff_pos_left, nat.zero_lt_one]
    end,

    ν(M) (pseudo_apply F (subst name.extend F'))
  using_well_founded {
    rel_tac := λ _ _,
      `[exact ⟨_, measure_wf (λ s,
          depth s.snd.snd.snd.fst + depth s.snd.snd.snd.snd) ⟩ ],
    dec_tac := do
      well_founded_tactics.unfold_wf_rel,
      well_founded_tactics.unfold_sizeof,

      tactic.dunfold_target [``depth, ``psigma.fst, ``psigma.snd],
      well_founded_tactics.cancel_nat_add_lt,
      tactic.try well_founded_tactics.trivial_nat_lt
  }

end concretion

end cpi
