import data.cpi.prefix_expr
import tactic.custom_wf

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

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
mutual inductive species, species.choices
with species : context → Type
| nil {Γ} : species Γ
| choice {Γ} : species.choices Γ → species Γ
| parallel {Γ} : species Γ → species Γ → species Γ
| restriction {Γ} (M : affinity) : species (context.extend M.arity Γ) → species Γ
with species.choices : context → Type
| nil {Γ} : species.choices Γ
| cons {Γ} {f} (π : prefix_expr Γ f) : species (f Γ) → species.choices Γ → species.choices Γ

reserve infixr ` |ₛ ` :50
infixr ` |ₛ ` := species.parallel

notation `ν(` M `) ` A := species.restriction M A

reserve prefix `Σ#`: 40
prefix `Σ# ` := species.choice


namespace species
  section rename
    /-- Apply a renaming function to a species. -/
    mutual def rename, rename.choice
    with rename : Π {Γ Δ : context}, (name Γ → name Δ) → species Γ → species Δ
    | Γ Δ ρ nil := nil
    | Γ Δ ρ (A |ₛ B) := rename ρ A |ₛ rename ρ B
    | Γ Δ ρ ν(M)A := ν(M)(rename (name.ext ρ) A)
    | Γ Δ ρ (Σ# As) := Σ# rename.choice ρ As
    with rename.choice : Π {Γ Δ : context}, (name Γ → name Δ) → species.choices Γ → species.choices Δ
    | Γ Δ ρ choices.nil := choices.nil
    | Γ Δ ρ (choices.cons π A As) :=
      let π' := prefix_expr.rename ρ π in
      let A' := rename (prefix_expr.ext π ρ) A in
      choices.cons π' A' (rename.choice ρ As)
    using_well_founded {
      rel_tac := λ _ _,
        `[exact ⟨_, measure_wf (λ s,
          -- Only decrease on the species, not the context.
          psum.cases_on s (λ x, sizeof x.snd.snd.snd) (λ x, sizeof x.snd.snd.snd))⟩ ],
      dec_tac := tactic.fst_dec_tac,
    }

    /-- Renaming with the identity function does nothing. -/
    lemma rename_id : ∀ {Γ} (A : species Γ), rename id A = A
    | Γ nil := by unfold rename
    | Γ (A |ₛ B) :=
      let a : rename id A = A := rename_id A in
      let b : rename id B = B := rename_id B in
      by simp [rename, a, b]
    | Γ ν(M)A :=
      let a : rename id A = A := rename_id A in
      by simp [rename, name.ext_id, a]
    | Γ (Σ# choices.nil) := by unfold rename rename.choice
    | Γ (Σ# choices.cons π A As) :=
      let π' : prefix_expr.rename id π = π := prefix_expr.rename_id π in
      let a : rename id A = A := rename_id A in
      let as : rename.choice id As = As := begin
        -- So it'd probably be more elegant to make the theorems mutually
        -- recursive too, but this'll do for now.
        have h := rename_id (Σ# As),
        simp only [rename] at h,
        from h
      end in
      begin
        unfold rename rename.choice at as ⊢,
        rw prefix_expr.ext_id,
        simp [π', a, as]
      end
    using_well_founded {
      rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, sizeof x.snd)⟩ ],
      dec_tac := tactic.fst_dec_tac,
    }

    /-- Renaming twice is the same as renaming with a composed function. -/
    lemma rename_compose :
      ∀ {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η) (A : species Γ)
      , rename σ (rename ρ A) = rename (σ ∘ ρ) A
    | Γ Δ η ρ σ  nil := by unfold rename
    | Γ Δ η ρ σ (A |ₛ B) :=
      let a := rename_compose ρ σ A in
      let b := rename_compose ρ σ B in
      by simp [rename, a, b]
    | Γ Δ η ρ σ ν(M)A :=
      let a := rename_compose (name.ext ρ) (name.ext σ) A in
      begin
        simp [rename, a],
        rw ← name.ext_comp ρ σ
      end
    | Γ Δ η ρ σ (Σ# choices.nil) := by unfold rename rename.choice
    | Γ Δ η ρ σ (Σ# choices.cons π A As) :=
      let π' := prefix_expr.rename_compose ρ σ π in
      let a := rename_compose (prefix_expr.ext π ρ) (prefix_expr.ext π σ) A in
      let as : rename.choice σ (rename.choice ρ As) = rename.choice (σ ∘ ρ) As := begin
        have h := rename_compose ρ σ (Σ# As),
        simp only [rename] at h,
        from h
      end in
      begin
        unfold rename rename.choice, simp [],
        rw ← prefix_expr.ext_comp ρ σ,
        rw ← prefix_expr.rename_ext ρ σ π,
        simp [π', a, as]
      end
    using_well_founded {
      rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ s, sizeof s.snd.snd.snd.snd.snd)⟩ ],
      dec_tac := tactic.fst_dec_tac,
    }

    lemma rename_ext
      {Γ Δ} {ρ : name Γ → name Δ} {n : ℕ} (A : species Γ)
      : rename name.extend (rename ρ A)
      = rename (name.ext ρ) (rename (@name.extend _ n) A)
      := by rw [rename_compose, ← name.ext_extend, rename_compose]
  end rename

  section free
    mutual def free_in, free_in.choices
    with free_in : ∀ {Γ}, level Γ → species Γ → Prop
    | Γ n nil := false
    | Γ n (A |ₛ B) := free_in n A ∨ free_in n B
    | Γ n (Σ# xs) := free_in.choices n xs
    | Γ n (ν(M) A) := free_in (level.extend n) A
    with free_in.choices : ∀ {Γ}, level Γ → species.choices Γ → Prop
    | Γ n choices.nil := false
    | Γ n (choices.cons π A As) := n ∈ π ∨ free_in (prefix_expr.lift_level π n) A ∨ free_in.choices n As
    using_well_founded {
      rel_tac := λ _ _,
        `[exact ⟨_, measure_wf (λ s, psum.cases_on s (λ x, sizeof x.snd.snd) (λ x, sizeof x.snd.snd))⟩ ],
      dec_tac := tactic.fst_dec_tac,
    }

    instance {Γ} : has_mem (level Γ) (species Γ) := ⟨ free_in ⟩

    private mutual def free_in_decide, free_in_decide.choices
    with free_in_decide : ∀ {Γ} (n) (A : species Γ), decidable (free_in n A)
    | Γ n nil := by { unfold free_in, from decidable.false }
    | Γ n (A |ₛ B) :=
      match free_in_decide n A with
      | is_true h := by { unfold free_in, from is_true (or.inl h) }
      | is_false h :=
        match free_in_decide n B with
        | is_true h' := by { unfold free_in, from is_true (or.inr h') }
        | is_false h' := by { unfold free_in, from is_false (not_or h h') }
        end
      end
    | Γ n (Σ# As) := by { unfold free_in, from free_in_decide.choices n As }
    | Γ n (ν(M) A) := by { unfold free_in, from free_in_decide (level.extend n) A }
    with free_in_decide.choices : ∀ {Γ} (n) (As : species.choices Γ), decidable (free_in.choices n As)
    | Γ n choices.nil := by { unfold free_in.choices, from decidable.false }
    | Γ n (choices.cons π A As) :=
      if h : n ∈ π then
        by { unfold free_in.choices, from is_true (or.inl h) }
      else
        match free_in_decide (prefix_expr.lift_level π n) A with
        | is_true h1 := by { unfold free_in.choices, from is_true (or.inr (or.inl h1)) }
        | is_false h1 :=
          match free_in_decide.choices n As with
          | is_true h2 := by { unfold free_in.choices, from is_true (or.inr (or.inr h2)) }
          | is_false h2 := by { unfold free_in.choices, from is_false (not_or h (not_or h1 h2)) }
          end
        end
    using_well_founded {
      rel_tac := λ _ _,
        `[exact ⟨_, measure_wf (λ s, psum.cases_on s (λ x, sizeof x.snd.snd) (λ x, sizeof x.snd.snd))⟩ ],
      dec_tac := tactic.fst_dec_tac,
    }

    instance free_in.decidable {Γ} {l} {A: species Γ} : decidable (free_in l A)
      := free_in_decide l A
  end free
end species

end cpi

#sanity_check
