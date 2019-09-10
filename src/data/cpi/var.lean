import data.cpi.basic

namespace cpi

namespace name
  /-- Scope extension for names. Given a renaming function, return the same
      function lifted one level.-/
  def ext :
    Π {Γ Δ : context}
    , (name Γ → name Δ)
    → ∀ {n : ℕ}, name (context.extend n Γ) → name (context.extend n Δ)
    | Γ Δ ρ n (name.nil lt) := name.nil lt
    | Γ Δ ρ n (name.extend x) := name.extend (ρ x)
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
  | Γ Δ ._ (a#(_; _)) ρ α := by { unfold augment at α ⊢, from name.ext ρ α }
  | Γ Δ ._ (τ@k) ρ α := by { unfold augment at α ⊢, from ρ α }

  /-- Augmenting with substituted prefix has the same effect as the original one. -/
  theorem subst_augment : ∀ {Γ Δ η} {ρ : name Γ → name Δ} {π : prefix_expr Γ}, augment π η = augment (subst ρ π) η
  | Γ Δ σ ρ (_#(_; _)) := by { unfold augment subst }
  | Γ Δ σ ρ (τ@_) := by { unfold augment subst }
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
    let π' := prefix_expr.subst ρ π in
    let A' : species (prefix_expr.augment (prefix_expr.subst ρ π) Δ) := begin
      have h : prefix_expr.augment π Δ = prefix_expr.augment (prefix_expr.subst ρ π) Δ
        := prefix_expr.subst_augment,
      rw (eq.symm h),
      from subst (prefix_expr.ext π ρ) A
    end in
    choices.cons π' A' (subst.choice ρ As)
  using_well_founded {
    rel_tac := λ _ _,
      `[exact ⟨_, measure_wf (λ (s : psum
        (Σ' {Γ Δ : context} (a : name Γ → name Δ), species Γ)
        (Σ' {Γ Δ : context} (a : name Γ → name Δ), choices Γ)),
        psum.cases_on s (λ x, sizeof x.snd.snd.snd) (λ x, sizeof x.snd.snd.snd))⟩ ],
    dec_tac := do
      well_founded_tactics.unfold_wf_rel,
      well_founded_tactics.unfold_sizeof,
      tactic.dunfold_target [``psigma.fst],
      tactic.try well_founded_tactics.cancel_nat_add_lt,
      well_founded_tactics.trivial_nat_lt
  }
end species

end cpi
