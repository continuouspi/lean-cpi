import data.cpi.semantics.interaction_tensor data.cpi.transition
import tactic.abel

namespace cpi

variables {ℂ ℍ : Type} {ω : context} [half_ring ℂ] [decidable_eq ℂ]

/-- Maps a potential transition to the interaction space. -/
def potential_interaction_space [cpi_equiv ℍ ω] {Γ} {ℓ : lookup ℍ ω Γ} {A : prime_species ℍ ω Γ}
  : transition.transition_from ℓ A.val
  → interaction_space ℂ ℍ ω Γ
| ⟨ _, # a , @production.concretion _ _ _ b y G, tr ⟩ := fin_fn.single ⟨ ⟦ A ⟧, ⟨ b, y, ⟦ G ⟧ ⟩, a ⟩ 1
| ⟨ _, τ@'_, E, tr ⟩ := 0
| ⟨ _, τ⟨_⟩, E, tr ⟩ := 0

lemma potential_interaction_space.equiv [cpi_equiv ℍ ω] {Γ} {ℓ : lookup ℍ ω Γ}
    {A B : prime_species ℍ ω Γ} :
  ∀ {k} {α : label ℍ Γ k} {E E' : production ℍ ω Γ k}
    {t : A.val [ℓ, α]⟶ E} {t' : B.val [ℓ, α]⟶ E'}
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

/-- Compute the potential interaction space for all transitions from a prime species. -/
def potential_interaction_space.from_prime [cpi_equiv ℍ ω] {Γ} (ℓ : lookup ℍ ω Γ) (A : prime_species ℍ ω Γ)
  : interaction_space ℂ ℍ ω Γ
  := finset.sum (fintype.elems (transition.transition_from ℓ A.val)) potential_interaction_space

/-- Compute the potential interaction space for all transitions from a species's prime conponents. -/
def potential_interaction_space.from_species [cpi_equiv ℍ ω] {Γ} (ℓ : lookup ℍ ω Γ) (A : species ℍ ω Γ)
  : interaction_space ℂ ℍ ω Γ
  := (cpi_equiv.prime_decompose A).sum' (potential_interaction_space.from_prime ℓ)

/-- `potential_interaction_space.from_species`, lifted to quotients. -/
def potential_interaction_space.from_species' [cpi_equiv_prop ℍ ω] {Γ} (ℓ : lookup ℍ ω Γ) (A : species' ℍ ω Γ)
  : interaction_space ℂ ℍ ω Γ := (cpi_equiv.prime_decompose' A).sum' (λ B, quot.lift_on B
    (potential_interaction_space.from_prime ℓ)
    (λ B₁ B₂ equ, begin
      cases cpi_equiv_prop.transition_iso ℓ equ with iso,
      let isoF := cpi_equiv_prop.transition_from_iso iso,
      suffices : ∀ x
        , (@potential_interaction_space ℂ ℍ ω _ _ _ _ ℓ _ x)
        = potential_interaction_space (isoF.to_fun x),
        from fintype.sum_iso _ _ isoF this,

      rintros ⟨ k, α, E, t ⟩,
      simp only [
        isoF, cpi_equiv_prop.transition_from_iso,
        cpi_equiv.transition_from_fwd, cpi_equiv.transition_from_inv],
      have eqE := (iso k α).2 E t,
      cases ((iso k α).fst).to_fun ⟨E, t⟩ with E' t',
      from potential_interaction_space.equiv equ eqE,
    end))

lemma potential_interaction_space.species_eq [cpi_equiv_prop ℍ ω] {Γ} {ℓ : lookup ℍ ω Γ} {A : species ℍ ω Γ}
  : (potential_interaction_space.from_species ℓ A : interaction_space ℂ ℍ ω Γ)
  = potential_interaction_space.from_species' ℓ ⟦ A ⟧
  := by simp only
    [potential_interaction_space.from_species, potential_interaction_space.from_species',
     quot.lift_on, quotient.mk, cpi_equiv.prime_decompose', multiset.sum',
     function.comp, multiset.map_map]

/-- Maps a spontaneous/immediate transition to a process space.

    This computes the Σ[x ∈ B [τ@k]—→ C] k and Σ[x ∈ B [τ⟨ a, b ⟩]—→ C] M(a, b)
    components of the definition of d(c ◯ A)/dt. -/
def immediate_process_space [cpi_equiv ℍ ω] {Γ} {ℓ : lookup ℍ ω Γ} (conc : ℍ ↪ ℂ)
    {A : prime_species ℍ ω Γ}
  : transition.transition_from ℓ A.val
  → process_space ℂ ℍ ω Γ
| ⟨ _, # a , _, tr ⟩ := 0
| ⟨ _, τ@'k, production.species B, tr ⟩ :=
  conc k • (to_process_space ⟦ B ⟧ - fin_fn.single ⟦ A ⟧ 1)
| ⟨ _, τ⟨ n ⟩, _, tr ⟩ := 0

lemma immediate_process_space.equiv [cpi_equiv ℍ ω] {Γ} {ℓ : lookup ℍ ω Γ} {conc : ℍ ↪ ℂ}
    {A B : prime_species ℍ ω Γ} :
  ∀ {k} {α : label ℍ Γ k} {E E' : production ℍ ω Γ k}
    {t : A.val [ℓ, α]⟶ E} {t' : B.val [ℓ, α]⟶ E'}
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
| _ (τ⟨ n ⟩) E E' t t' eqA eqE := rfl

/-- Compute the immediate process space for all transitions from a prime species. -/
def immediate_process_space.from_prime [cpi_equiv ℍ ω] {Γ} (conc : ℍ ↪ ℂ) (ℓ : lookup ℍ ω Γ)
    (A : prime_species ℍ ω Γ)
  : process_space ℂ ℍ ω Γ
  := finset.sum (fintype.elems (transition.transition_from ℓ A.val)) (immediate_process_space conc)

/-- Compute the immediate process space for all transitions from a species's prime conponents. -/
def immediate_process_space.from_species [cpi_equiv ℍ ω] {Γ} (conc : ℍ ↪ ℂ) (ℓ : lookup ℍ ω Γ) (A : species ℍ ω Γ)
  : process_space ℂ ℍ ω Γ
  := (cpi_equiv.prime_decompose A).sum' (immediate_process_space.from_prime conc ℓ)

/-- `immediate_process_space.from_species`, lifted to quotients. -/
def immediate_process_space.from_species' [cpi_equiv_prop ℍ ω] {Γ} (conc : ℍ ↪ ℂ) (ℓ : lookup ℍ ω Γ) (A : species' ℍ ω Γ)
  : process_space ℂ ℍ ω Γ := (cpi_equiv.prime_decompose' A).sum' (λ B, quot.lift_on B
    (immediate_process_space.from_prime conc ℓ)
    (λ B₁ B₂ equ, begin
      cases cpi_equiv_prop.transition_iso ℓ equ with iso,
      let isoF := cpi_equiv_prop.transition_from_iso iso,
      suffices : ∀ x
        , immediate_process_space conc x
        = immediate_process_space conc (isoF.to_fun x),
        from fintype.sum_iso _ _ isoF this,

      rintros ⟨ k, α, E, t ⟩,
      simp only [
        isoF, cpi_equiv_prop.transition_from_iso,
        cpi_equiv.transition_from_fwd, cpi_equiv.transition_from_inv],
      have eqE := (iso k α).2 E t,
      cases ((iso k α).fst).to_fun ⟨E, t⟩ with E' t',
      from immediate_process_space.equiv equ eqE,
    end))

lemma immediate_process_space.species_eq [cpi_equiv_prop ℍ ω] {Γ} {conc : ℍ ↪ ℂ} {ℓ : lookup ℍ ω Γ} {A : species ℍ ω Γ}
  : immediate_process_space.from_species conc ℓ A
  = immediate_process_space.from_species' conc ℓ ⟦ A ⟧
  := by simp only
    [immediate_process_space.from_species, immediate_process_space.from_species',
     quot.lift_on, quotient.mk, cpi_equiv.prime_decompose', multiset.sum',
     function.comp, multiset.map_map]

/-- The vector space of potential interactions of a process (∂P). -/
def process_potential [cpi_equiv ℍ ω] {Γ} (ℓ : lookup ℍ ω Γ)
  : process ℂ ℍ ω Γ → interaction_space ℂ ℍ ω Γ
| (c ◯ A) := c • potential_interaction_space.from_species ℓ A
| (P |ₚ Q) := process_potential P + process_potential Q

lemma process_potential.nil_zero [cpi_equiv ℍ ω] {Γ} (ℓ : lookup ℍ ω Γ) (c : ℂ)
  : process_potential ℓ (c ◯ nil) = 0
  := by simp only
      [process_potential, potential_interaction_space.from_species,
       cpi_equiv.prime_decompose_nil, multiset.sum'_zero, smul_zero]

/-- The vector space of immediate actions of a process (dP/dt)-/
def process_immediate [cpi_equiv ℍ ω]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil)) (conc : ℍ ↪ ℂ)
  : process ℂ ℍ ω (context.extend M.arity context.nil)
  → process_space ℂ ℍ ω (context.extend M.arity context.nil)
| (c ◯ A)
  := c • immediate_process_space.from_species conc ℓ A
  + (½ : ℂ) • (process_potential ℓ (c ◯ A) ⊘[conc] process_potential ℓ (c ◯ A))
| (P |ₚ Q)
  := process_immediate P + process_immediate Q
   + (process_potential ℓ P ⊘[conc] process_potential ℓ Q)

lemma process_immediate.nil_zero {conc : ℍ ↪ ℂ} [cpi_equiv ℍ ω]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
    (c : ℂ)
  : process_immediate M ℓ conc (c ◯ nil) = 0
  := by simp only
      [process_immediate, immediate_process_space.from_species,
       process_potential.nil_zero, cpi_equiv.prime_decompose_nil,
       multiset.sum'_zero, interaction_tensor.zero_left, smul_zero, add_zero]

lemma process_potential.equiv [cpi_equiv_prop ℍ ω] {Γ} (ℓ : lookup ℍ ω Γ) :
  ∀ {P Q : process ℂ ℍ ω Γ}
  , P ≈ Q → process_potential ℓ P = process_potential ℓ Q
| P Q eq := begin
  induction eq,
  case process.equiv.refl { refl },
  case process.equiv.trans : P Q R ab bc ih_ab ih_bc { from trans ih_ab ih_bc },
  case process.equiv.symm : P Q eq ih { from symm ih },
  case process.equiv.ξ_species : c A B equ {
    suffices : potential_interaction_space.from_species ℓ A
             = potential_interaction_space.from_species ℓ B,
    { simp only [process_potential],  from congr_arg ((•) c) this },

    calc  potential_interaction_space.from_species ℓ A
        = potential_interaction_space.from_species' ℓ ⟦ A ⟧ : potential_interaction_space.species_eq
    ... = potential_interaction_space.from_species' ℓ ⟦ B ⟧ : by rw quotient.sound equ
    ... = potential_interaction_space.from_species ℓ B : potential_interaction_space.species_eq.symm
  },
  case process.equiv.ξ_parallel₁ : P P' Q eq ih {
    unfold process_potential, rw ih,
  },
  case process.equiv.ξ_parallel₂ : P Q Q' eq ih {
    unfold process_potential, rw ih,
  },
  case process.equiv.parallel_nil : P C {
    show process_potential ℓ P + process_potential ℓ (C ◯ nil) = process_potential ℓ P,
    simp only [process_potential.nil_zero, add_zero],
  },
  case cpi.process.equiv.parallel_symm { simp only [process_potential, add_comm] },
  case process.equiv.parallel_assoc { simp only [process_potential, add_assoc] },
  case process.equiv.join : A c d { simp only [process_potential, add_smul] },
  case process.equiv.split : A B c {
    simp only [process_potential, potential_interaction_space.from_species,
               cpi_equiv.prime_decompose_parallel, multiset.sum'_add, smul_add],
  },
end

private lemma process_immediate.join [cpi_equiv_prop ℍ ω] (M : affinity ℍ)
    (ℓ : lookup ℍ ω (context.extend M.arity context.nil)) {conc : ℍ ↪ ℂ} (c d : ℂ)
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

private lemma process_immediate.split [cpi_equiv_prop ℍ ω] [add_monoid ℍ]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
    (conc : ℍ ↪ ℂ) (c : ℂ)
    (A B : species ℍ ω (context.extend M.arity context.nil))
  : process_immediate M ℓ conc (c ◯ (A |ₛ B))
  = process_immediate M ℓ conc (c ◯ A |ₚ c ◯ B) := begin
  simp only [process_immediate, immediate_process_space.from_species,
             process_potential.equiv ℓ process.equiv.split,
             cpi_equiv.prime_decompose_parallel, multiset.sum'_add, smul_add],

  generalize : multiset.sum' (cpi_equiv.prime_decompose A) (immediate_process_space.from_prime conc ℓ) = dA,
  generalize : multiset.sum' (cpi_equiv.prime_decompose B) (immediate_process_space.from_prime conc ℓ) = dB,

  have : process_potential ℓ (c ◯ A |ₚ c ◯ B) = process_potential ℓ (c ◯ A) + process_potential ℓ (c ◯ B)
    := rfl,
  simp only [this],

  generalize : process_potential ℓ (c ◯ A) = pA,
  generalize : process_potential ℓ (c ◯ B) = pB,

  simp only [interaction_tensor.left_distrib, interaction_tensor.right_distrib, smul_add],
  rw interaction_tensor.comm pB pA,

  generalize : ½ • pA ⊘[conc] pA = iA,
  generalize : ½ • pB ⊘[conc] pB = iB,
  generalize : pA ⊘[conc] pB = iAB,

  calc  c • dA + c • dB + (iA + (½ : ℂ) • iAB + ((½ : ℂ) • iAB + iB))
      = c • dA + c • dB + (iA + iB + ((½ : ℂ) • iAB + (½ : ℂ) • iAB)) : by abel
  ... = c • dA + c • dB + (iA + iB + iAB)
        : by rw [← add_smul, ← half_ring.one_is_two_halves, one_smul]
  ... = c • dA + iA + (c • dB + iB) + iAB : by abel
end

lemma process_immediate.equiv [cpi_equiv_prop ℍ ω] [add_monoid ℍ]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
    (conc : ℍ ↪ ℂ)
  : ∀ {P Q : process ℂ ℍ ω (context.extend M.arity context.nil)}
  , P ≈ Q
  → process_immediate M ℓ conc P
  = process_immediate M ℓ conc Q
| P Q eq := begin
  induction eq,
  case process.equiv.refl { from rfl },
  case process.equiv.symm : A B eq ih { from (symm ih) },
  case process.equiv.trans : P Q R ab bc ih_ab ih_bc { from trans ih_ab ih_bc },

  case process.equiv.ξ_species : c A B equ {
    suffices : immediate_process_space.from_species conc ℓ A
             = immediate_process_space.from_species conc ℓ B,
    { simp only [process_immediate],
      rw [process_potential.equiv ℓ (process.equiv.ξ_species equ), this]
    },

    calc  immediate_process_space.from_species conc ℓ A
        = immediate_process_space.from_species' conc ℓ ⟦ A ⟧ : immediate_process_space.species_eq
    ... = immediate_process_space.from_species' conc ℓ ⟦ B ⟧ : by rw quotient.sound equ
    ... = immediate_process_space.from_species conc ℓ B : immediate_process_space.species_eq.symm
  },
  case process.equiv.ξ_parallel₁ : P P' Q eq ih {
    simp only [process_immediate, process_potential.equiv ℓ eq, ih],
  },
  case process.equiv.ξ_parallel₂ : P Q Q' eq ih {
    simp only [process_immediate, process_potential.equiv ℓ eq, ih],
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

    generalize : process_potential ℓ P = p,
    generalize : process_potential ℓ Q = q,
    generalize : process_potential ℓ R = r,

    calc  p ⊘ q + (p + q) ⊘ r
        = p ⊘[conc] q + p ⊘[conc] r + q ⊘ r : by rw [interaction_tensor.left_distrib, add_assoc]
    ... = q ⊘[conc] r + p ⊘[conc] q + p ⊘[conc] r : by simp only [add_comm, add_left_comm, interaction_tensor.comm]
    ... = q ⊘[conc] r + p ⊘[conc] (q + r) : by rw [add_assoc, ← interaction_tensor.right_distrib]
  },
  case process.equiv.join : A c d {
    simp only [process_immediate, process_potential],

    generalize : potential_interaction_space.from_species ℓ A = Ds,
    generalize : immediate_process_space.from_species conc ℓ A = Ps,

    suffices
      : (c • Ds) ⊘[conc] (d • Ds) + ((½ : ℂ) • ((c • Ds) ⊘[conc] (c • Ds)) + (½ : ℂ) • (d • Ds) ⊘[conc] (d • Ds))
      = (½ : ℂ) • ((c • Ds + d • Ds) ⊘[conc] (c • Ds + d • Ds)),
      { simp only [add_assoc, add_comm, add_smul, add_left_comm, this] },

    from process_immediate.join M ℓ c d Ds Ps,
  },
  case process.equiv.split : A B c {
    from process_immediate.split M ℓ conc c A B
  },
end

/-- dP/dt lifted to quotients. -/
def process_immediate.quot [cpi_equiv_prop ℍ ω] [add_monoid ℍ]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
    (conc : ℍ ↪ ℂ)
  : process' ℂ ℍ ω (context.extend M.arity context.nil)
  → process_space ℂ ℍ ω (context.extend M.arity context.nil)
| P := quot.lift_on P (process_immediate M ℓ conc)
    (λ P Q, process_immediate.equiv M ℓ conc)

/-- dP/dt lifted to process spaces. -/
def process_immediate.space [cpi_equiv_prop ℍ ω] [half_ring ℍ]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
    (conc : ℍ ↪ ℂ)
  : process_space ℂ ℍ ω (context.extend M.arity context.nil)
  → process_space ℂ ℍ ω (context.extend M.arity context.nil)
| P := process_immediate.quot M ℓ conc (process.from_space P)

end cpi

#lint-
