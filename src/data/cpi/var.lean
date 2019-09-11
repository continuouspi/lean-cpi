import data.cpi.basic

import tactic.basic

namespace cpi

/-- Create an equality for the identity function. -/
private def lift_id {α : Type} {f : α → α} (eq : ∀ x, f x = x) : f = id := begin
  have h : (λ x, f x) = id,
    simp only [eq],
    from rfl,
  simp only [] at h,
  from h
end

namespace name
  /-- Scope extension for names. Given a renaming function, return the same
      function lifted one level.-/
  def ext :
    Π {Γ Δ : context}
    , (name Γ → name Δ)
    → ∀ {n : ℕ}, name (context.extend n Γ) → name (context.extend n Δ)
    | Γ Δ ρ n (name.nil lt) := name.nil lt
    | Γ Δ ρ n (name.extend x) := name.extend (ρ x)

  /-- Extending with the identity does nothing. -/
  theorem ext_identity :
    ∀ {Γ : context} {n : ℕ} {α : name (context.extend n Γ)}
    , ext id α = α
  | Γ n (name.nil p) := by unfold ext
  | Γ n (name.extend α) := by unfold ext id

  /-- Extending with the identity yields the identity function. -/
  theorem ext_id : ∀ {Γ : context} {n : ℕ}, @ext Γ Γ id n = id
  | Γ n := lift_id (@ext_identity Γ n)

  /-- Composing extensions is equivalent extending a composition. -/
  theorem ext_compose :
    ∀ {Γ Δ η} {ρ : name Γ → name Δ} {σ : name Δ → name η} {n : ℕ} {α : name  (context.extend n Γ)}
    , ext σ (ext ρ α) = ext (σ ∘ ρ) α
  | Γ Δ η ρ σ n (name.nil p) := by simp only [ext]
  | Γ Δ η ρ σ n (name.extend α) := by simp only [ext]

  /-- Composing extensions is equivalent extending a composition. -/
  theorem ext_comp :
    ∀ {Γ Δ η} {ρ : name Γ → name Δ} {σ : name Δ → name η} {n : ℕ}
    , (ext σ ∘ ext ρ) = @ext _ _ (σ ∘ ρ) n
  | Γ Δ η ρ σ n := funext (@ext_compose Γ Δ η ρ σ n)
end name

namespace prefix_expr
  /-- Apply a renaming function to a prefix. -/
  def subst : Π {Γ Δ : context}, (name Γ → name Δ) → prefix_expr Γ → prefix_expr Δ
    | Γ Δ ρ (a#(b; y)) := (ρ a)#(list.map ρ b; y)
    | Γ Δ ρ τ@k := τ@k

  /-- Scope extension for prefix expressions. Given a renaming function, return
      the same function lifted for the variables bound by this prefix. -/
  def ext :
    Π {Γ Δ η : context} (π : prefix_expr η)
    , (name Γ → name Δ)
    → name (augment π Γ) → name (augment π Δ)
  | Γ Δ ._ (a#(b; y)) ρ α := by { unfold augment at α ⊢, from name.ext ρ α }
  | Γ Δ ._ (τ@k) ρ α := by { unfold augment at α ⊢, from ρ α }

  /-- Extending with the identity does nothing. -/
  theorem ext_identity :
    ∀ {Γ η : context} {π : prefix_expr η} {α : name (augment π Γ)}
    , ext π id α = α
  | Γ η (a#(b; y)) α := begin
      unfold ext,
      rw name.ext_identity,
      from rfl
    end
  | Γ η (τ@k) name := by { unfold ext id, from rfl }

  /-- Extending with the identity yields the identity function. -/
  theorem ext_id : ∀ {Γ η : context} {π : prefix_expr η}, @ext Γ Γ η π id = id
  | Γ η π := lift_id (@ext_identity Γ η π)

  /-- Composing extensions is equivalent extending a composition. -/
  theorem ext_compose :
    ∀ {Γ Δ η φ} {ρ : name Γ → name Δ} {σ : name Δ → name η} {π : prefix_expr φ} {α : name (augment π Γ)}
    , ext π σ (ext π ρ α) = ext π (σ ∘ ρ) α
  | Γ Δ η φ ρ σ (a#(b; y)) α := begin
      unfold ext,
      rw ← @name.ext_compose _ _ _ ρ σ,
      from rfl,
    end
  | Γ Δ η φ ρ σ (τ@k) α := by { unfold ext, from rfl }

  /-- Composing extensions is equivalent extending a composition. -/
  theorem ext_comp :
    ∀ {Γ Δ η φ} {ρ : name Γ → name Δ} {σ : name Δ → name η} {π : prefix_expr φ}
    , (ext π σ ∘ ext π ρ) = ext π (σ ∘ ρ)
  | Γ Δ η φ ρ σ π := funext (@ext_compose Γ Δ η φ ρ σ π)

  /-- Augmenting with a substituted prefix has the same effect as the original one. -/
  theorem subst_augment : ∀ {Γ Δ η} {ρ : name Γ → name Δ} {π : prefix_expr Γ}, augment π η = augment (subst ρ π) η
  | Γ Δ η ρ (_#(_; _)) := by { unfold augment subst }
  | Γ Δ η ρ (τ@_) := by { unfold augment subst }

  /-- Extending with a substituted prefix has the same effect as the original one. -/
  theorem subst_ext :
    ∀ {Γ Δ η φ} {ρ : name Γ → name Δ} {σ : name η → name φ} {π : prefix_expr Γ}
    , @ext η φ Γ π σ == (@ext η φ Δ (subst ρ π) σ)
  | Γ Δ η φ ρ σ (a#(b; y)) := begin
      have eq_a : @ext η φ Γ (a#(b ; y)) σ = name.ext σ :=
        let h : ∀ α, @ext η φ Γ (a#(b ; y)) σ α = name.ext σ α :=
          λ α, by { unfold ext, from rfl }
        in funext h,
      have eq_b : @ext η φ Δ (subst ρ (a#(b ; y))) σ = name.ext σ :=
        let h : ∀ α, @ext η φ Δ (ρ a#(@list.map (name Γ) (name Δ) ρ b ; y)) σ α = name.ext σ α :=
          λ α, by { unfold ext, from rfl }
        in funext h,
      rw [eq_a, eq_b]
    end
  | Γ Δ η φ ρ σ (τ@k) := begin
      have eq_a : @ext η φ Γ (τ@k) σ = σ :=
        let h : ∀ α, @ext η φ Γ (τ@k) σ α = σ α :=
          λ α, by { unfold ext, from rfl }
        in funext h,
      have eq_b : @ext η φ Δ (subst ρ (τ@k)) σ = σ :=
        let h : ∀ α, @ext η φ Δ (τ@k) σ α = σ α :=
          λ α, by { unfold ext, from rfl }
        in funext h,
      rw [eq_a, eq_b]
    end

  /-- Substituting with the identity function does nothing. -/
  theorem subst_id : ∀ {Γ} (π : prefix_expr Γ), subst id π = π
  | Γ (a#(b; y)) := by simp [subst]
  | Γ (τ@_) := by unfold augment subst

  /-- Substituting twice is the same as substituting on a composed function. -/
  theorem subst_compose :
    ∀ {Γ Δ η} {ρ : name Γ → name Δ} {σ : name Δ → name η} (π : prefix_expr Γ)
    , subst σ (subst ρ π) = subst (σ ∘ ρ) π
  | Γ Δ η ρ σ (a#(b; y)) := by simp [subst]
  | Γ Δ η ρ σ (τ@_) := by unfold augment subst
end prefix_expr

namespace species
  /-- Apply a renaming function to a species. -/
  mutual def subst, subst.choice
  with subst : Π {Γ Δ : context}, (name Γ → name Δ) → species Γ → species Δ
  | Γ Δ ρ nil := nil
  | Γ Δ ρ (A |ₛ B) := subst ρ A |ₛ subst ρ B
  | Γ Δ ρ ν(M)A := ν(M)(subst (name.ext ρ) A)
  | Γ Δ ρ (choice As) := choice (subst.choice ρ As)
  with subst.choice : Π {Γ Δ : context}, (name Γ → name Δ) → species.choices Γ → species.choices Δ
  | Γ Δ ρ choices.nil := choices.nil
  | Γ Δ ρ (choices.cons π A As) :=
    (let π' := prefix_expr.subst ρ π in
    let A' : species (prefix_expr.augment (prefix_expr.subst ρ π) Δ) := begin
      rw ← @prefix_expr.subst_augment _ _ Δ ρ π,
      from subst (prefix_expr.ext π ρ) A
    end in
    choices.cons π' A' (subst.choice ρ As))
  using_well_founded {
    rel_tac := λ _ _,
      `[exact ⟨_, measure_wf (λ s,
        psum.cases_on s (λ x, sizeof x.snd.snd.snd) (λ x, sizeof x.snd.snd.snd))⟩ ],
    dec_tac := tactic.fst_dec_tac,
  }

  /-- Substituting with the identity function does nothing. -/
  theorem subst_id : ∀ {Γ} (A : species Γ), subst id A = A
  | Γ nil := by unfold subst
  | Γ (A |ₛ B) :=
    let a : subst id A = A := subst_id A in
    let b : subst id B = B := subst_id B in
    by simp [subst, a, b]
  | Γ ν(M)A :=
    let a : subst id A = A := subst_id A in
    by simp [subst, name.ext_id, a]
  | Γ (choice choices.nil) := by unfold subst subst.choice
  | Γ (choice (choices.cons π A As)) :=
    let π' : prefix_expr.subst id π = π := prefix_expr.subst_id π in
    let a : subst id A = A := subst_id A in
    let as : subst.choice id As = As := begin
      have h := subst_id (choice As),
      simp only [subst] at h,
      from h
    end in
    begin
      unfold subst subst.choice at as ⊢,
      rw prefix_expr.ext_id,
      simp [π', a, as]
    end
  using_well_founded {
    rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ s, sizeof s.snd)⟩ ],
    dec_tac := tactic.fst_dec_tac,
  }

  section x
    parameters {Γ Δ η : context} {ρ : name Γ → name Δ} {σ : name Δ → name η}
    parameters {π : prefix_expr Γ} {A : species (prefix_expr.augment π Γ)}

    def a := @eq.mpr
      (species (prefix_expr.augment (prefix_expr.subst σ (prefix_expr.subst ρ π)) η))
      (species (prefix_expr.augment (prefix_expr.subst ρ π) η))
      (by rw @prefix_expr.subst_augment _ _ _ σ _)
      (subst
        (prefix_expr.ext (prefix_expr.subst ρ π) σ)
        (@eq.mpr
          (species (prefix_expr.augment (prefix_expr.subst ρ π) Δ))
          (species (prefix_expr.augment π Δ))
          (by rw @prefix_expr.subst_augment _ _ _ ρ π)
          (subst (prefix_expr.ext π ρ) A)))

    def b := @eq.mpr
      (species (prefix_expr.augment (prefix_expr.subst (σ ∘ ρ) π) η))
      (species (prefix_expr.augment π η))
      (by rw @prefix_expr.subst_augment _ _ _ (σ ∘ ρ) _)
      (subst (prefix_expr.ext π (σ ∘ ρ)) A)

    def a_eq_b : a == b :=
      let eq_1
         : eq.mpr rfl (subst (prefix_expr.ext π (σ ∘ ρ)) A)
        == eq.mpr rfl (subst (prefix_expr.ext π (σ ∘ ρ)) A)
        := heq.rfl in

      let is_2
        : species (prefix_expr.augment (prefix_expr.subst (σ ∘ ρ) π) η)
        = species (prefix_expr.augment π η)
        := by rw @prefix_expr.subst_augment _ _ _ (σ ∘ ρ) _ in
      let eq_2
         : eq.mpr rfl (subst (prefix_expr.ext π (σ ∘ ρ)) A)
        == eq.mpr is_2 (subst (prefix_expr.ext π (σ ∘ ρ)) A)
        := symm is_2 ▸ eq_1 in

      let eq_3
        : eq.mpr rfl (eq.mpr rfl (subst (prefix_expr.ext π (σ ∘ ρ)) A))
       == eq.mpr is_2 (subst (prefix_expr.ext π (σ ∘ ρ)) A)
       := heq.symm (heq.symm eq_2)
      in

      let is_32
        : species (prefix_expr.augment (prefix_expr.subst ρ π) Δ)
        = species (prefix_expr.augment π Δ)
        := by rw @prefix_expr.subst_augment _ _ _ ρ _ in

      sorry
  end x

  -- set_option pp.implicit true

  -- theorem subst_compose :
  --   ∀ {Γ Δ η} {ρ : name Γ → name Δ} {σ : name Δ → name η} (A : species Γ)
  --   , subst σ (subst ρ A) = subst (σ ∘ ρ) A
  -- | Γ Δ η ρ σ  nil := by unfold subst
  -- | Γ Δ η ρ σ (A |ₛ B) :=
  --   let a : subst σ (subst ρ A) = subst (σ ∘ ρ) A := subst_compose A in
  --   let b : subst σ (subst ρ B) = subst (σ ∘ ρ) B := subst_compose B in
  --   by simp [subst, a, b]
  -- | Γ Δ η ρ σ ν(M)A :=
  --   let a : subst (name.ext σ) (subst (name.ext ρ) A) = subst _ A := subst_compose A in
  --   begin
  --     simp [subst, a],
  --     rw ← @name.ext_comp _ _ _ ρ σ
  --   end
  -- | Γ Δ η ρ σ (choice choices.nil) := by unfold subst subst.choice
  -- | Γ Δ η ρ σ (choice (choices.cons π A As)) :=
  --   let π' : prefix_expr.subst σ (prefix_expr.subst ρ π) = prefix_expr.subst (σ ∘ ρ) π
  --     := prefix_expr.subst_compose π in
  --   let a : subst (prefix_expr.ext π σ) (subst (prefix_expr.ext π ρ) A) = subst _ A := subst_compose A in
  --   let as : subst.choice σ (subst.choice ρ As) = subst.choice (σ ∘ ρ) As := begin
  --     have h := subst_compose (choice As),
  --     simp only [subst] at h,
  --     from h
  --   end in
  --   begin
  --     have h : prefix_expr.ext π σ == prefix_expr.ext (prefix_expr.subst ρ π) σ
  --       := prefix_expr.subst_ext,
  --     unfold subst subst.choice at as ⊢,
  --     simp [π', a, as],
  --     -- rw ← @prefix_expr.ext_comp _ _ _ _ ρ σ,
  --     -- rw prefix_expr.subst_augment,
  --   end
  -- using_well_founded {
  --   rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ s, sizeof s.snd.snd.snd.snd.snd)⟩ ],
  --   dec_tac := tactic.fst_dec_tac,
  -- }
end species

end cpi
