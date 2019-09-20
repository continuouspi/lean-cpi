import data.cpi.basic
import tactic.basic

set_option profiler true
set_option profiler.threshold 0.5

namespace cpi

namespace name
  /-- Scope extension for names. Given a renaming function, return the same
      function lifted one level.-/
  def ext :
    Π {Γ Δ : context}
    , (name Γ → name Δ)
    → ∀ {n : ℕ}, name (context.extend n Γ) → name (context.extend n Δ)
    | Γ Δ ρ n (nil idx) := nil idx
    | Γ Δ ρ n (extend x) := extend (ρ x)

  /-- Extending with the identity does nothing. -/
  theorem ext_identity :
    ∀ {Γ : context} {n : ℕ} (α : name (context.extend n Γ))
    , ext id α = α
  | Γ n (nil lt) := rfl
  | Γ n (extend α) := rfl

  /-- Extending with the identity yields the identity function. -/
  theorem ext_id : ∀ {Γ : context} {n : ℕ}, @ext Γ Γ id n = id
  | Γ n := funext ext_identity

  /-- Composing extensions is equivalent extending a composition. -/
  theorem ext_compose :
    ∀ {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η) {n : ℕ} (α : name (context.extend n Γ))
    , ext σ (ext ρ α) = ext (σ ∘ ρ) α
  | Γ Δ η ρ σ n (nil lt) := rfl
  | Γ Δ η ρ σ n (extend α) := rfl

  /-- Composing extensions is equivalent extending a composition. -/
  theorem ext_comp :
    ∀ {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η) {n : ℕ}
    , (ext σ ∘ ext ρ) = @ext _ _ (σ ∘ ρ) n
  | Γ Δ η ρ σ n := funext (ext_compose ρ σ)

  /-- Extending then renaming with an extended function, is equivalent to
      renaming then extending. -/
  theorem ext_extend :
    ∀ {Γ Δ} {n : ℕ} (ρ : name Γ → name Δ)
    , (ext ρ ∘ extend) = (@extend Δ n ∘ ρ)
  | Γ Δ n ρ := funext (λ x, rfl)

  def swap {Γ} {M N : ℕ}
    : name (context.extend M (context.extend N Γ))
    → name (context.extend N (context.extend M Γ))
  | (nil lt) := extend (nil lt)
  | (extend (nil lt)) := nil lt
  | (extend (extend n)) := extend (extend n)

  theorem swap.ext_ext {Γ Δ} {ρ : name Γ → name Δ} {m n : ℕ}
    : (ext (ext ρ) ∘ swap)
    = (swap ∘ @ext _ _ (@ext _ _ ρ m) n) := funext $ λ α,
      match α with
      | nil p := by simp [swap, ext]
      | extend (nil lt) := by simp [swap, ext]
      | extend (extend _) := by simp [swap, ext]
      end

  theorem swap.comp_extend {Γ} {m n : ℕ}
    : (@name.swap Γ m n ∘ name.extend) = (name.ext name.extend) := funext $ λ α,
      match α with
      | nil idx := by simp [swap, ext]
      | extend n := by simp [swap, ext]
      end

  theorem swap.comp_ext_extend {Γ} {m n : ℕ}
    : (@name.swap Γ m n ∘ name.ext name.extend) = name.extend := funext $ λ α,
      match α with
      | nil idx := by simp [swap, ext]
      | extend n := by simp [swap, ext]
      end
end name

namespace prefix_expr
  /-- Apply a renaming function to a prefix. -/
  def rename : Π {Γ Δ : context} {f}, (name Γ → name Δ) → prefix_expr Γ f → prefix_expr Δ f
    | Γ Δ f ρ (a#(b; y)) := (ρ a)#(list.map ρ b; y)
    | Γ Δ f ρ τ@k := τ@k

  /-- Scope extension for prefix expressions. Given a renaming function, return
      the same function lifted for the variables bound by this prefix. -/
  def ext :
    Π {Γ Δ η : context} {f} (π : prefix_expr η f)
    , (name Γ → name Δ)
    → name (f Γ) → name (f Δ)
  | Γ Δ ._ ._ (a#(b; y)) ρ α := name.ext ρ α
  | Γ Δ ._ ._ τ@k ρ α := ρ α

  /-- Extending with the identity does nothing. -/
  theorem ext_identity :
    ∀ {Γ η : context} {f} (π : prefix_expr η f) (α : name (f Γ))
    , ext π id α = α
  | Γ η ._ (a#(b; y)) α := name.ext_identity α
  | Γ η ._ τ@k name := rfl

  /-- Extending with the identity yields the identity function. -/
  theorem ext_id : ∀ {Γ η : context} {f} (π : prefix_expr η f), @ext Γ Γ η f π id = id
  | Γ η f π := funext (ext_identity π)

  /-- Composing extensions is equivalent extending a composition. -/
  theorem ext_compose :
    ∀ {Γ Δ η φ} {f} (ρ : name Γ → name Δ) (σ : name Δ → name η)
      (π : prefix_expr φ f) (α : name (f Γ))
    , ext π σ (ext π ρ α) = ext π (σ ∘ ρ) α
  | Γ Δ η φ f ρ σ (a#(b; y)) α := name.ext_compose ρ σ α
  | Γ Δ η φ f ρ σ τ@k α := rfl

  /-- Composing extensions is equivalent extending a composition. -/
  theorem ext_comp :
    ∀ {Γ Δ η φ} {f} (ρ : name Γ → name Δ) (σ : name Δ → name η) (π : prefix_expr φ f)
    , (ext π σ ∘ ext π ρ) = ext π (σ ∘ ρ)
  | Γ Δ η φ f ρ σ π := funext (ext_compose ρ σ π)

  /-- Extending with a renamed prefix has the same effect as the original one. -/
  theorem rename_ext :
    ∀ {Γ Δ η φ} {f} (ρ : name Γ → name Δ) (σ : name η → name φ) (π : prefix_expr Γ f)
    , @ext η φ Γ f π σ = (ext (rename ρ π) σ)
  | Γ Δ η φ f ρ σ (a#(b; y)) := funext (λ α, rfl)
  | Γ Δ η φ f ρ σ τ@k := funext (λ α, rfl)

  /-- Renaming with the identity function does nothing. -/
  theorem rename_id : ∀ {Γ} {f} (π : prefix_expr Γ f), rename id π = π
  | Γ ._ (a#(b; y)) := by simp [rename]
  | Γ ._ τ@k := rfl

  /-- Renaming twice is the same as renaming with a composed function. -/
  theorem rename_compose :
    ∀ {Γ Δ η} {f} (ρ : name Γ → name Δ) (σ : name Δ → name η) (π : prefix_expr Γ f)
    , rename σ (rename ρ π) = rename (σ ∘ ρ) π
  | Γ Δ η f ρ σ (a#(b; y)) := by simp [rename]
  | Γ Δ η f ρ σ (τ@_) := rfl
end prefix_expr

namespace species
  /-- Apply a renaming function to a species. -/
  mutual def rename, rename.choice
  with rename : Π {Γ Δ : context}, (name Γ → name Δ) → species Γ → species Δ
  | Γ Δ ρ nil := nil
  | Γ Δ ρ (A |ₛ B) := rename ρ A |ₛ rename ρ B
  | Γ Δ ρ ν(M)A := ν(M)(rename (name.ext ρ) A)
  | Γ Δ ρ (choice As) := choice (rename.choice ρ As)
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
  theorem rename_id : ∀ {Γ} (A : species Γ), rename id A = A
  | Γ nil := by unfold rename
  | Γ (A |ₛ B) :=
    let a : rename id A = A := rename_id A in
    let b : rename id B = B := rename_id B in
    by simp [rename, a, b]
  | Γ ν(M)A :=
    let a : rename id A = A := rename_id A in
    by simp [rename, name.ext_id, a]
  | Γ (choice choices.nil) := by unfold rename rename.choice
  | Γ (choice (choices.cons π A As)) :=
    let π' : prefix_expr.rename id π = π := prefix_expr.rename_id π in
    let a : rename id A = A := rename_id A in
    let as : rename.choice id As = As := begin
      -- So it'd probably be more elegant to make the theorems mutually
      -- recursive too, but this'll do for now.
      have h := rename_id (choice As),
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
  theorem rename_compose :
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
  | Γ Δ η ρ σ (choice choices.nil) := by unfold rename rename.choice
  | Γ Δ η ρ σ (choice (choices.cons π A As)) :=
    let π' := prefix_expr.rename_compose ρ σ π in
    let a := rename_compose (prefix_expr.ext π ρ) (prefix_expr.ext π σ) A in
    let as : rename.choice σ (rename.choice ρ As) = rename.choice (σ ∘ ρ) As := begin
      have h := rename_compose ρ σ (choice As),
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

  protected lemma rename_ext
    {Γ Δ} {ρ : name Γ → name Δ} {n : ℕ} (A : species Γ)
    : rename name.extend (rename ρ A)
    = rename (name.ext ρ) (rename (@name.extend _ n) A)
    := by rw [rename_compose, ← name.ext_extend, rename_compose]
end species

end cpi

-- | For sanity checking only. This takes a long time to run normally.
run_cmd sanity_check
#sanity_check
