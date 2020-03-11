import data.cpi.semantics.interaction_tensor data.cpi.transition
import tactic.abel algebra.distrib_embedding

namespace cpi

variables {ℂ ℍ : Type} {ω : context} [half_ring ℂ] [decidable_eq ℂ]
  {M : affinity ℍ}
  {ℓ : lookup ℍ ω (context.extend M.arity context.nil)}

/-- Maps a potential transition to the interaction space. -/
def potential_interaction_space [cpi_equiv ℍ ω] {Γ} {ℓ : lookup ℍ ω Γ} {A : species ℍ ω Γ}
  : transition.transition_from ℓ A
  → interaction_space ℂ ℍ ω Γ
| ⟨ _, # a , @production.concretion _ _ _ b y G, tr ⟩ := fin_fn.single ⟨ ⟦ A ⟧, ⟨ b, y, ⟦ G ⟧ ⟩, a ⟩ 1
| ⟨ _, τ@'_, E, tr ⟩ := 0
| ⟨ _, τ⟨_⟩, E, tr ⟩ := 0

lemma potential_interaction_space.equiv [cpi_equiv ℍ ω]
  {Γ} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ} :
  ∀ {k} {α : label ℍ Γ k} {E E' : production ℍ ω Γ k}
    {t : A [ℓ, α]⟶ E} {t' : B [ℓ, α]⟶ E'}
  , A ≈ B → E ≈ E'
  → @potential_interaction_space ℂ ℍ ω _ _ _ Γ ℓ _ (transition.transition_from.mk t)
  = potential_interaction_space (transition.transition_from.mk t')
| _ (# a) (@production.concretion _ _ _ b y E) (production.concretion E') t t' eqA (production.equiv.concretion eqE) := begin
  unfold transition.transition_from.mk potential_interaction_space,
  have : ⟦ A ⟧ = ⟦ B ⟧ := quot.sound eqA,
  have : ⟦ E ⟧ = ⟦ E' ⟧ := quot.sound eqE,
  rw [‹⟦ A ⟧ = ⟦ B ⟧›, ‹⟦ E ⟧ = ⟦ E' ⟧›],
end
| _ (τ@'_) E E' t t' _ _ := rfl
| _ (τ⟨_⟩) E E' t t' _ _ := rfl

/-- Maps a spontanious/immediate transition to a process space.

    This computes the Σ[x ∈ B [τ@k]—→ C] k and Σ[x ∈ B [τ⟨ a, b ⟩]—→ C] M(a, b)
    components of the definition of d(c ◯ A)/dt. -/
def immediate_process_space [cpi_equiv ℍ ω]
    {A : species ℍ ω (context.extend M.arity context.nil)}
    (conc : ℍ ↪ ℂ)
  : transition.transition_from ℓ A
  → process_space ℂ ℍ ω (context.extend M.arity context.nil)
| ⟨ _, # a , _, tr ⟩ := 0
| ⟨ _, τ@'k, production.species B, tr ⟩ :=
  conc k • (to_process_space ⟦ B ⟧ - to_process_space ⟦ A ⟧)
| ⟨ _, τ⟨ n ⟩, production.species B, tr ⟩ :=
  let arity := quot.lift_on n
    (λ ⟨ a, b ⟩, M.f (name.to_idx a) (name.to_idx b))
    (λ ⟨ a₁, b₁ ⟩ ⟨ a₂, b₂ ⟩ eq, begin
      rcases eq with ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩ | ⟨ ⟨ _ ⟩, ⟨ _ ⟩ ⟩,
      from rfl,
      from M.symm (name.to_idx a₁) (name.to_idx b₁),
    end) in
  option.cases_on arity 0 (λ k, conc k • (to_process_space ⟦ B ⟧ - to_process_space ⟦ A ⟧))

lemma immediate_process_space.equiv [cpi_equiv ℍ ω]
    {A B : species ℍ ω (context.extend M.arity context.nil)} {conc : ℍ ↪ ℂ}
  : ∀ {k} {α : label ℍ (context.extend M.arity context.nil) k}
      {E E' : production ℍ ω (context.extend M.arity context.nil) k}
      {t : A [ℓ, α]⟶ E} {t' : B [ℓ, α]⟶ E'}
    , A ≈ B → E ≈ E'
    → immediate_process_space conc (transition.transition_from.mk t)
    = immediate_process_space conc (transition.transition_from.mk t')
| _ (# a ) E E' t t' eqA eqE := rfl
| _ (τ@'k) (production.species E) (production.species E') t t' eqA (production.equiv.species eqE) := begin
  unfold transition.transition_from.mk immediate_process_space,
  have : ⟦ A ⟧ = ⟦ B ⟧ := quot.sound eqA,
  have : ⟦ E ⟧ = ⟦ E' ⟧ := quot.sound eqE,
  rw [‹⟦ A ⟧ = ⟦ B ⟧›, ‹⟦ E ⟧ = ⟦ E' ⟧›],
end
| _ (τ⟨ n ⟩) (production.species E) (production.species E') t t' eqA (production.equiv.species eqE) := begin
  unfold transition.transition_from.mk immediate_process_space,
  have : ⟦ A ⟧ = ⟦ B ⟧ := quot.sound eqA,
  have : ⟦ E ⟧ = ⟦ E' ⟧ := quot.sound eqE,
  rw [‹⟦ A ⟧ = ⟦ B ⟧›, ‹⟦ E ⟧ = ⟦ E' ⟧›],
end

/-- The vector space of potential interactions of a process (∂P). -/
noncomputable def process_potential [cpi_equiv ℍ ω]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
  : process ℂ ℍ ω (context.extend M.arity context.nil)
  → interaction_space ℂ ℍ ω (context.extend M.arity context.nil)
| (c ◯ A) := c • finset.sum (fintype.elems (transition.transition_from ℓ A)) potential_interaction_space
| (P |ₚ Q) := process_potential P + process_potential Q


lemma process_potential.nil_zero [cpi_equiv ℍ ω]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil)) (c : ℂ)
  : process_potential M ℓ (c ◯ nil) = 0 := begin
  simp only [process_potential],

  -- We have that there are no possible transitions, and thus the sum is 0.
  have : fintype.elems (transition.transition_from ℓ nil) = ∅
      := finset.eq_empty_of_forall_not_mem (λ ⟨ k, α, E, t ⟩, by cases t),
  simp only [this, finset.sum_empty, smul_zero],
end

/-- The vector space of immediate actions of a process (dP/dt)-/
noncomputable def process_immediate [cpi_equiv ℍ ω]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil)) (conc : ℍ ↪ ℂ)
  : process ℂ ℍ ω (context.extend M.arity context.nil)
  → process_space ℂ ℍ ω (context.extend M.arity context.nil)
| (c ◯ A) := c • finset.sum (fintype.elems (transition.transition_from ℓ A)) (immediate_process_space conc)
  + (½ : ℂ) • (process_potential M ℓ (c ◯ A) ⊘[conc] process_potential M ℓ (c ◯ A))
| (P |ₚ Q)
  := process_immediate P + process_immediate Q
   + (process_potential M ℓ P ⊘[conc] process_potential M ℓ Q)

lemma process_immediate.nil_zero {conc : ℍ ↪ ℂ} [cpi_equiv ℍ ω]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
    (c : ℂ)
  : process_immediate M ℓ conc (c ◯ nil) = 0 := begin
  simp only [process_immediate, process_potential.nil_zero M ℓ c],

  -- We have that there are no possible transitions, and thus the sum is 0.
  have : fintype.elems (transition.transition_from ℓ nil) = ∅
      := finset.eq_empty_of_forall_not_mem (λ ⟨ k, α, E, t ⟩, by cases t),
  simp only [this, finset.sum_empty, interaction_tensor.zero_left, smul_zero, add_zero],
end

lemma process_potential.equiv [cpi_equiv_prop ℍ ω]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
  : ∀ {P Q : process ℂ ℍ ω (context.extend M.arity context.nil)}
  , P ≈ Q → process_potential M ℓ P = process_potential M ℓ Q
| P Q eq := begin
  induction eq,
  case process.equiv.refl { refl },
  case process.equiv.trans : P Q R ab bc ih_ab ih_bc { from trans ih_ab ih_bc },
  case process.equiv.symm : P Q eq ih { from symm ih },
  case process.equiv.ξ_species : c A B eq {
    simp only [process_potential],

    suffices
      : finset.sum (fintype.elems (transition.transition_from ℓ A)) potential_interaction_space
      = finset.sum (fintype.elems (transition.transition_from ℓ B)) potential_interaction_space,
      from congr_arg (has_scalar.smul _) this,

    cases cpi_equiv_prop.transition_iso ℓ eq with iso,
    let isoF := cpi_equiv_prop.transition_from_iso iso,
    suffices : ∀ x
      , potential_interaction_space x
      = potential_interaction_space (isoF.to_fun x),
      from fintype.sum_iso potential_interaction_space potential_interaction_space isoF this,

    rintros ⟨ k, α, E, t ⟩,
    simp only [
      isoF, cpi_equiv_prop.transition_from_iso,
      cpi_equiv.transition_from_fwd, cpi_equiv.transition_from_inv],
    have eqE := (iso k α).2 E t,
    cases ((iso k α).fst).to_fun ⟨E, t⟩ with E' t',
    from potential_interaction_space.equiv eq eqE,
  },
  case process.equiv.ξ_parallel₁ : P P' Q eq ih {
    unfold process_potential, rw ih,
  },
  case process.equiv.ξ_parallel₂ : P Q Q' eq ih {
    unfold process_potential, rw ih,
  },
  case process.equiv.parallel_nil : P C {
    unfold1 process_potential,
    show process_potential M ℓ P + process_potential M ℓ (C ◯ nil)
       = process_potential M ℓ P,

    have : process_potential M ℓ (C ◯ nil) = 0 := process_potential.nil_zero M ℓ C,
    simp only [this, add_zero],
  },
  case cpi.process.equiv.parallel_symm { simp only [process_potential, add_comm] },
  case process.equiv.parallel_assoc { simp only [process_potential, add_assoc] },
  case process.equiv.join : A c d { simp only [process_potential, add_smul] },
end

private lemma process_immediate.join [cpi_equiv_prop ℍ ω] {conc : ℍ ↪ ℂ} (c d : ℂ)
    (Ds : interaction_space ℂ ℍ ω (context.extend (M.arity) context.nil))
    (Ps : process_space ℂ ℍ ω (context.extend (M.arity) context.nil))
  : (c • Ds) ⊘[conc] (d • Ds) + ((½ : ℂ) • (c • Ds) ⊘[conc] (c • Ds) + (½ : ℂ) • (d • Ds) ⊘[conc] (d • Ds))
  = (½ : ℂ) • (c • Ds + d • Ds) ⊘[conc] (c • Ds + d • Ds) := begin
  generalize ehalf : (½ : ℂ) = half,

  rw [interaction_tensor.left_distrib (c • Ds) (d • Ds),
      interaction_tensor.right_distrib (c • Ds),
      interaction_tensor.right_distrib (d • Ds),
      interaction_tensor.comm (d • Ds) (c • Ds)],

  calc  (c • Ds) ⊘ (d • Ds)
      + (half • (c • Ds) ⊘ (c • Ds) + half • (d • Ds) ⊘ (d • Ds))

      = (1 : ℂ) • (c • Ds) ⊘[conc] (d • Ds)
      + (half • (c • Ds) ⊘[conc] (c • Ds) + half • (d • Ds) ⊘[conc] (d • Ds))
      : by simp only [one_smul]

  ... = (half + half) • (c • Ds) ⊘[conc] (d • Ds)
      + (half • (c • Ds) ⊘[conc] (c • Ds) + half • (d • Ds) ⊘[conc] (d • Ds))
      : by rw [half_ring.one_is_two_halves, ← ehalf]

       ... = half • (c • Ds) ⊘[conc] (c • Ds) + half • (c • Ds) ⊘[conc] (d • Ds)
           + (half • (c • Ds) ⊘[conc] (d • Ds) + half • (d • Ds) ⊘[conc] (d • Ds))
           : begin
             simp only [add_smul],
             generalize : half • (c • Ds) ⊘[conc] (d • Ds) = cd,
             generalize : half • (c • Ds) ⊘[conc] (c • Ds) = cc,
             generalize : half • (d • Ds) ⊘[conc] (d • Ds) = dd,
             abel,
            end

       ... = half • ((c • Ds) ⊘ (c • Ds) + (c • Ds) ⊘ (d • Ds)
                    + ((c • Ds) ⊘ (d • Ds) + (d • Ds) ⊘ (d • Ds)))
           : by simp only [smul_add]
end

lemma process_immediate.equiv [cpi_equiv_prop ℍ ω] [add_monoid ℍ]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
    (conc : distrib_embedding ℍ ℂ (+) (+))
  : ∀ {P Q : process ℂ ℍ ω (context.extend M.arity context.nil)}
  , P ≈ Q
  → process_immediate M ℓ conc.to_embed P
  = process_immediate M ℓ conc.to_embed Q
| P Q eq := begin
  induction eq,
  case process.equiv.refl { from rfl },
  case process.equiv.symm : A B eq ih { from (symm ih) },
  case process.equiv.trans : P Q R ab bc ih_ab ih_bc { from trans ih_ab ih_bc },

  case process.equiv.ξ_species : c A B eq {
    simp only [process_immediate],

    suffices : finset.sum (fintype.elems (transition.transition_from ℓ A)) (immediate_process_space conc.to_embed)
             = finset.sum (fintype.elems (transition.transition_from ℓ B)) (immediate_process_space conc.to_embed),
    { have eql : process_potential M ℓ (c ◯ A) = process_potential M ℓ (c ◯ B)
        := process_potential.equiv M ℓ (process.equiv.ξ_species eq),
      rw [this, eql] },

    cases cpi_equiv_prop.transition_iso ℓ eq with iso,
    let isoF := cpi_equiv_prop.transition_from_iso iso,
    suffices : ∀ x
      , immediate_process_space conc.to_embed x
      = immediate_process_space conc.to_embed (isoF.to_fun x),
      from fintype.sum_iso (immediate_process_space _) (immediate_process_space _) isoF this,

    rintros ⟨ k, α, E, t ⟩,
    simp only [
      isoF, cpi_equiv_prop.transition_from_iso,
      cpi_equiv.transition_from_fwd, cpi_equiv.transition_from_inv],
    have eqE := (iso k α).2 E t,
    cases ((iso k α).fst).to_fun ⟨E, t⟩ with E' t',
    from immediate_process_space.equiv eq eqE,
  },
  case process.equiv.ξ_parallel₁ : P P' Q eq ih {
    unfold process_immediate,
    rw [process_potential.equiv M ℓ eq, ih],
  },
  case process.equiv.ξ_parallel₂ : P Q Q' eq ih {
    unfold process_immediate,
    rw [process_potential.equiv M ℓ eq, ih],
  },
  case process.equiv.parallel_nil {
    simp only [process_immediate, process_immediate.nil_zero, add_zero,
               process_potential.nil_zero, interaction_tensor.zero_left],
  },
  case cpi.process.equiv.parallel_symm : P Q {
    simp only [process_immediate, add_comm, interaction_tensor.comm],
  },
  case process.equiv.parallel_assoc : P Q R {
    simp only [process_immediate, add_assoc] ,
    simp only [add_left_comm],
    refine congr_arg _ _,
    refine congr_arg _ _,
    refine congr_arg _ _,

    unfold process_potential,

    generalize : process_potential M ℓ P = p,
    generalize : process_potential M ℓ Q = q,
    generalize : process_potential M ℓ R = r,

    calc  p ⊘ q + (p + q) ⊘ r
        = p ⊘[conc] q + p ⊘[conc] r + q ⊘ r : by rw [interaction_tensor.left_distrib, add_assoc]
    ... = q ⊘[conc] r + p ⊘[conc] q + p ⊘[conc] r : by simp only [add_comm, add_left_comm, interaction_tensor.comm]
    ... = q ⊘[conc] r + p ⊘[conc] (q + r) : by rw [add_assoc, ← interaction_tensor.right_distrib]
  },
  case process.equiv.join : A c d {
    simp only [process_immediate, process_potential],

    generalize : finset.sum (fintype.elems (transition.transition_from ℓ A)) potential_interaction_space = Ds,
    generalize : finset.sum (fintype.elems (transition.transition_from ℓ A)) (immediate_process_space conc.to_embed) = Ps,

    suffices
      : (c • Ds) ⊘[conc.to_embed] (d • Ds) + ((½ : ℂ) • ((c • Ds) ⊘[conc.to_embed] (c • Ds)) + (½ : ℂ) • (d • Ds) ⊘[conc.to_embed] (d • Ds))
      = (½ : ℂ) • ((c • Ds + d • Ds) ⊘[conc.to_embed] (c • Ds + d • Ds)),
      { simp only [add_assoc, add_comm, add_smul, add_left_comm, this] },

    from process_immediate.join c d Ds Ps,
  }
end

/-- dP/dt lifted to quotients. -/
noncomputable def process_immediate.quot [cpi_equiv_prop ℍ ω] [add_monoid ℍ]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
    (conc : distrib_embedding ℍ ℂ (+) (+))
  : process' ℂ ℍ ω (context.extend M.arity context.nil)
  → process_space ℂ ℍ ω (context.extend M.arity context.nil)
| P := quot.lift_on P (process_immediate M ℓ conc.to_embed)
    (λ P Q, process_immediate.equiv M ℓ conc)

/-- dP/dt lifted to process spaces. -/
noncomputable def process_immediate.space [cpi_equiv_prop ℍ ω] [half_ring ℍ]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
    (conc : distrib_embedding ℍ ℂ (+) (+))
  : process_space ℂ ℍ ω (context.extend M.arity context.nil)
  → process_space ℂ ℍ ω (context.extend M.arity context.nil)
| P := process_immediate.quot M ℓ conc (process.from_space P)

end cpi

#lint-
