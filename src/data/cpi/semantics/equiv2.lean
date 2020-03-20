import data.cpi.semantics.basic

namespace cpi

/-
 The proof that "exenteded process equivalence (i.e. the additional c∘(A|B) ≡⁺ c∘A|c∘B rule).
 This is effectively split into three parts:

  - Firstly, we show an ismomorphism between transitions from (A|B), and
    transitions from A, from B, and the (com₁ intersection of the two).

    As part of this, we show that the two sets have equivalence semantics.

  - We then show that finset.sum f (all A|B) = finset.sum f (all A + all B)
    (or some variation of) where f is the function to compute the
    interaction/process space.

  - These lemmas are plugged into the join case for induction over
    `process.equiv2` - the res of those proofs is largely the same as what is
    found in the main equivalence.
-/

variables {ℂ ℍ : Type} {ω : context} [half_ring ℂ] [cpi_equiv_prop ℍ ω] [add_monoid ℍ] [decidable_eq ℂ]
  {M : affinity ℍ}
  {ℓ : lookup ℍ ω (context.extend M.arity context.nil)}
  (conc : distrib_embedding ℍ ℂ (+) (+))

/-- S standalone version of `transition.com₁` -/
private def com₁_of {Γ} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ) :=
  (Σ (x y : ℕ) (a b : name Γ)
     (F : concretion ℍ ω Γ x y) (G : concretion ℍ ω Γ y x)
  , transition A ℓ (#a) (production.concretion F) × transition B ℓ (#b) (production.concretion G))

/-- Mark com₁_of as decidable -/
private noncomputable def com₁_of.decidable_eq {Γ} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ) :
  decidable_eq (com₁_of ℓ A B) := classical.dec_eq _

/-- Just introduce this as an axiom. Would be good to do in the future, if we
    ever get actual transition enumerating -/
private constant com₁_of.fintype {Γ : context} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ)
  : fintype (com₁_of ℓ A B)

private noncomputable def transition.transition_eq {ℍ} {ω} {Γ} (ℓ : lookup ℍ ω Γ) (A : species ℍ ω Γ) :
  decidable_eq (transition.transition_from ℓ A) := classical.dec_eq _
local attribute [instance] transition.transition_eq com₁_of.decidable_eq com₁_of.fintype

private def com₁_of.to_transition {Γ : context} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ}
  : com₁_of ℓ A B → transition.transition_from ℓ (A |ₛ B)
| ⟨ x, y, a, b, F, G, tf, tg ⟩ := ⟨ _, _, _, transition.com₁ rfl rfl tf tg ⟩

private lemma com₁_of.interaction_zero {Γ} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ} :
  ∀ (t : com₁_of ℓ A B)
  , potential_interaction_space (com₁_of.to_transition t)
  = (0 : interaction_space ℂ ℍ ω Γ)
| ⟨ x, y, a, b, F, G, tf, tg ⟩ := rfl

/-- Wraps all three kinds of transitions from A|ₛB. -/
private def par_of {Γ : context} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ) :=
  (transition.transition_from ℓ A ⊕ transition.transition_from ℓ B) ⊕ com₁_of ℓ A B

/-- `potential_interaction_space` lifted to par_of. -/
@[pattern]
private def par_of.potential_interaction_space {A B : species ℍ ω (context.extend M.arity context.nil)}
  : par_of ℓ A B → interaction_space ℂ ℍ ω (context.extend M.arity context.nil)
  := sum.elim
      (sum.elim potential_interaction_space potential_interaction_space)
      (potential_interaction_space ∘ com₁_of.to_transition)

/-- `immediate_process_space` lifted to par_of. -/
@[pattern]
private def par_of.immediate_process_space {A B : species ℍ ω (context.extend M.arity context.nil)}
  : par_of ℓ A B → process_space ℂ ℍ ω (context.extend M.arity context.nil)
  := sum.elim
      (sum.elim (immediate_process_space conc.to_embed) (immediate_process_space conc.to_embed))
      (immediate_process_space conc.to_embed ∘ com₁_of.to_transition)

private def par_of.of_transition {Γ : context} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ} :
  ∀ {k} {α : label ℍ Γ k} {E}, (A |ₛ B) [ℓ, α]⟶ E → par_of ℓ A B
| _ _ _ (transition.parL_species _ t) := sum.inl (sum.inl ⟨ _, _, _, t ⟩)
| _ _ _ (transition.parL_concretion _ t) := sum.inl (sum.inl ⟨ _, _, _, t ⟩)
| _ _ _ (transition.parR_species _ t) := sum.inl (sum.inr ⟨ _, _, _, t ⟩)
| _ _ _ (transition.parR_concretion _ t) := sum.inl (sum.inr ⟨ _, _, _, t ⟩)
| _ _ _ (transition.com₁ rfl rfl tf tg) := sum.inr ⟨ _, _, _, _, _, _, tf, tg ⟩

private def par_of.of_transition_from {Γ : context} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ} :
  transition.transition_from ℓ (A |ₛ B) → par_of ℓ A B
| ⟨ _, _, _, t ⟩ := par_of.of_transition t

private def par_of.to_transition {Γ : context} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ} :
  par_of ℓ A B → transition.transition_from ℓ (A |ₛ B)
  := sum.elim (sum.elim (transition.parL A B) (transition.parR A B)) com₁_of.to_transition

private def par_of.iso {Γ : context} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ)
  : transition.transition_from ℓ (A |ₛ B) ≃ par_of ℓ A B :=
  { to_fun := par_of.of_transition_from,
    inv_fun := par_of.to_transition,
    left_inv := λ x, begin
      rcases x with ⟨ k, α, E, t ⟩,
      cases t;
      simp only [par_of.of_transition_from, par_of.of_transition, par_of.to_transition, sum.elim, transition.parL, transition.parR],
      cases t_a_1, cases t_a_2,
      from rfl,
    end,
    right_inv := λ x, begin
      rcases x with ⟨ ⟨ k, α, ⟨ E | E ⟩, t ⟩ | ⟨ k, α, ⟨ E | E ⟩, t ⟩ ⟩ | ⟨ x, y, a, b, F, G, tf, tg ⟩;
      simp only [par_of.of_transition, par_of.of_transition_from, par_of.to_transition,
                 com₁_of.to_transition, transition.parL, transition.parR, sum.elim],
    end }

private lemma par_of.complete {Γ : context} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ)
  : ∀ (t : par_of ℓ A B)
  , t ∈ (finset.image sum.inl
           ( finset.image sum.inl (fintype.elems (transition.transition_from ℓ A))
           ∪ finset.image sum.inr (fintype.elems (transition.transition_from ℓ B)))
         ∪ finset.image sum.inr (fintype.elems (com₁_of ℓ A B)))
| (sum.inr t) := finset.mem_union_right _ (finset.mem_image_of_mem sum.inr (fintype.complete t))
| (sum.inl t) := finset.mem_union_left _ (begin
    cases t; refine finset.mem_image_of_mem _ _,
    from finset.mem_union_left _ (finset.mem_image_of_mem _ (fintype.complete t)),
    from finset.mem_union_right _ (finset.mem_image_of_mem _ (fintype.complete t)),
  end)

private lemma par_of.potential_eq
  {A B : species ℍ ω (context.extend M.arity context.nil)}
  (ξ : interaction_space ℂ ℍ ω (context.extend M.arity context.nil)) :
  ∀ (t : transition.transition_from ℓ (A |ₛ B))
  , potential_interaction_space t ⊘[conc.to_embed] ξ
  = par_of.potential_interaction_space (par_of.of_transition_from t) ⊘[conc.to_embed] ξ
| ⟨ k, α, E, t ⟩ := begin
  cases t;
  simp only [
    par_of.of_transition_from, par_of.of_transition, par_of.potential_interaction_space,
    com₁_of.to_transition, sum.elim, function.comp
  ],

  case transition.parL_species : α { cases α; from rfl },
  case transition.parR_species : α { cases α; from rfl },

  case transition.parL_concretion : α b y F {
    cases α with _ a, simp only [potential_interaction_space],
    from interaction_tensor.parallel₁ A B F a 1 ξ,
  },
  case transition.parR_concretion : α b y F {
    cases α with _ a, simp only [potential_interaction_space],
    from interaction_tensor.parallel₂ A B F a 1 ξ,
  },
  case transition.com₁ : b y x y F G FG α eqF eqα {
    subst eqF, subst eqα, from rfl
  },
end


private lemma par_of.immediate_eq {A B : species ℍ ω (context.extend M.arity context.nil)} :
  ∀ (t : transition.transition_from ℓ (A |ₛ B))
  , immediate_process_space conc.to_embed t
  = (sum.elim (sum.elim (immediate_process_space conc.to_embed) (immediate_process_space conc.to_embed))
          ((immediate_process_space conc.to_embed) ∘ com₁_of.to_transition)) (par_of.of_transition_from t)
| (⟨ k, α, E, @transition.parL_species _ _ _ _ _ B _ C t ⟩) := begin
  simp only [par_of.of_transition, par_of.of_transition_from, sum.elim],

  have proc_eq : to_process_space ⟦C |ₛ B⟧ - to_process_space ⟦A |ₛ B⟧
               = to_process_space ⟦C⟧ - to_process_space ⟦A⟧,
  {
    calc  (to_process_space ⟦C |ₛ B⟧ : process_space ℂ ℍ ω _) - to_process_space ⟦A |ₛ B⟧
        = to_process_space ⟦C⟧ + to_process_space ⟦B⟧ - (to_process_space ⟦A⟧ + to_process_space ⟦B⟧)
          : by rw [to_process_space.parallel C B, to_process_space.parallel A B]
    ... = to_process_space ⟦C⟧ - to_process_space ⟦A⟧ : by abel
  },

  cases α; { simp only [immediate_process_space], rw proc_eq },
end
| (⟨ k, α, E, @transition.parL_concretion _ _ _ _ _ _ _ F _ C t ⟩)
  := by { cases α, from rfl }
| (⟨ k, α, E, @transition.parR_species _ _ _ _ _ B _ C t ⟩) := begin
  simp only [par_of.of_transition, par_of.of_transition_from, sum.elim],

  have proc_eq : to_process_space ⟦A |ₛ C⟧ - to_process_space ⟦A |ₛ B⟧
               = to_process_space ⟦C⟧ - to_process_space ⟦B⟧,
  {
    calc  (to_process_space ⟦A |ₛ C⟧ : process_space ℂ ℍ ω _) - to_process_space ⟦A |ₛ B⟧
        = to_process_space ⟦A⟧ + to_process_space ⟦C⟧ - (to_process_space ⟦A⟧ + to_process_space ⟦B⟧)
          : by rw [to_process_space.parallel A C, to_process_space.parallel A B]
    ... = to_process_space ⟦C⟧ - to_process_space ⟦B⟧ : by abel
  },

  cases α; { simp only [immediate_process_space], rw proc_eq },
end
| (⟨ k, α, E, @transition.parR_concretion _ _ _ _ _ _ _ F _ C t ⟩)
  := by { cases α, from rfl }
| (⟨ k, α, E, transition.com₁ rfl rfl tf tg ⟩) := rfl

lemma process_potential.split
  (A B : species ℍ ω (context.extend (M.arity) context.nil))
  (ξ : interaction_space ℂ ℍ ω (context.extend M.arity context.nil))
: finset.sum (fintype.elems (transition.transition_from ℓ (A |ₛ B))) potential_interaction_space
  ⊘[conc.to_embed] ξ
= ( finset.sum (fintype.elems (transition.transition_from ℓ A)) potential_interaction_space
  + finset.sum (fintype.elems (transition.transition_from ℓ B)) potential_interaction_space )
  ⊘[conc.to_embed] ξ
:=
  have distrib_interaction : ∀ α (ts : finset α) (f : α → interaction_space ℂ ℍ ω _)
         , finset.sum ts f ⊘[conc.to_embed] ξ
         = finset.sum ts (λ t, f t ⊘[conc.to_embed] ξ),
  {
    assume α ts f,
    simp only [interaction_tensor.comm],
    from symm (finset.sum_hom ts (interaction_tensor conc.to_embed ξ)),
  },

  calc  finset.sum (fintype.elems (transition.transition_from ℓ (A |ₛ B))) potential_interaction_space ⊘[conc.to_embed] ξ

      = finset.sum (fintype.elems (transition.transition_from ℓ (A |ₛ B)))
          (λ (t : transition.transition_from ℓ (A |ₛ B)), potential_interaction_space t ⊘[conc.to_embed] ξ)
      : by rw distrib_interaction

  ... = finset.sum
        (finset.image sum.inl
            (finset.image sum.inl (fintype.elems (transition.transition_from ℓ A)) ∪
                finset.image sum.inr (fintype.elems (transition.transition_from ℓ B))) ∪
          finset.image sum.inr (fintype.elems (com₁_of ℓ A B)))
        (λ (t : (transition.transition_from ℓ A ⊕ transition.transition_from ℓ B) ⊕ com₁_of ℓ A B),
          sum.elim (sum.elim potential_interaction_space potential_interaction_space)
              (potential_interaction_space ∘ com₁_of.to_transition)
              t ⊘[conc.to_embed] ξ)
      : finset.sum_iso
          (λ t, potential_interaction_space t ⊘[conc.to_embed] ξ)
          (λ t, par_of.potential_interaction_space t ⊘[conc.to_embed] ξ)
          (par_of.iso ℓ A B)
          (λ t, par_of.potential_eq conc ξ t)
          (fintype.elems _)
          ( finset.image sum.inl
              ( finset.image sum.inl (fintype.elems (transition.transition_from ℓ A))
              ∪ finset.image sum.inr (fintype.elems (transition.transition_from ℓ B)) )
            ∪ finset.image sum.inr (fintype.elems (com₁_of ℓ A B)) )
          (λ x _, par_of.complete ℓ A B _)
          (λ x _, fintype.complete _)

  ... = ( finset.sum (fintype.elems (transition.transition_from ℓ A)) potential_interaction_space
        + finset.sum (fintype.elems (transition.transition_from ℓ B)) potential_interaction_space
        + finset.sum (fintype.elems (com₁_of ℓ A B)) (potential_interaction_space ∘ com₁_of.to_transition) )
        ⊘[conc.to_embed] ξ
        : by rw [ ← finset.sum_sum_elim, ← finset.sum_sum_elim, distrib_interaction]

  ... = ( finset.sum (fintype.elems (transition.transition_from ℓ A)) potential_interaction_space
        + finset.sum (fintype.elems (transition.transition_from ℓ B)) potential_interaction_space)
        ⊘[conc.to_embed] ξ : begin
          have : finset.sum (fintype.elems (com₁_of ℓ A B)) (potential_interaction_space ∘ com₁_of.to_transition)
               = (0 : interaction_space ℂ ℍ ω _)
               := finset.sum_eq_zero (λ t _, com₁_of.interaction_zero t),
          rw [this, add_zero],
        end

axiom process_immediate.split
  (A B : species ℍ ω (context.extend M.arity context.nil))
: finset.sum (fintype.elems (transition.transition_from ℓ (A |ₛ B))) (immediate_process_space conc.to_embed)
= finset.sum (fintype.elems (transition.transition_from ℓ A)) (immediate_process_space conc.to_embed)
+ finset.sum (fintype.elems (transition.transition_from ℓ B)) (immediate_process_space conc.to_embed)

lemma process_potential.equiv2
  : ∀ {P Q : process ℂ ℍ ω (context.extend M.arity context.nil)}
    (ξ : interaction_space ℂ ℍ ω (context.extend M.arity context.nil))
  , P ≡⁺ Q
  → process_potential M ℓ P ⊘[conc.to_embed] ξ = process_potential M ℓ Q ⊘[conc] ξ
| P Q ξ eq := begin
  induction eq,
  case process.equiv2.refl { from rfl, },
  case process.equiv2.symm : P Q _ ih { from symm ih },
  case process.equiv2.trans : P Q R _ _ pq qr { from trans pq qr },
  case process.equiv2.ξ_species : c A B eq {
    rw process_potential.equiv M ℓ (process.equiv.ξ_species eq),
    from rfl,
  },
  case process.equiv2.ξ_parallel₁ : P P' Q eq ih {
    simp only [process_potential, interaction_tensor.left_distrib, ih],
    from rfl,
  },
  case process.equiv2.ξ_parallel₂ : P Q Q' eq ih {
    simp only [process_potential, interaction_tensor.left_distrib, ih],
    from rfl,
  },

  case process.equiv2.parallel_nil {
    rw process_potential.equiv M ℓ process.equiv.parallel_nil,
    from rfl,
  },
  case process.equiv2.parallel_symm {
    rw process_potential.equiv M ℓ process.equiv.parallel_symm,
    from rfl,
  },
  case process.equiv2.parallel_assoc {
    rw process_potential.equiv M ℓ process.equiv.parallel_assoc,
    from rfl,
  },
  case process.equiv2.join {
    rw process_potential.equiv M ℓ process.equiv.join,
    from rfl,
  },

  case process.equiv2.split : A B c {
    simp only [process_potential, interaction_tensor.left_distrib],
    unfold_coes,
    rw [← interaction_tensor.left_distrib, ← smul_add, ← interaction_tensor.smul, ← interaction_tensor.smul],
    rw process_potential.split conc A B ξ,
  },
end

lemma process_immediate.equiv2
  : ∀ {P Q : process ℂ ℍ ω (context.extend M.arity context.nil)}
  , P ≡⁺ Q → process_immediate M ℓ conc.to_embed P = process_immediate M ℓ conc.to_embed Q
| P Q eq := begin
  induction eq,
  case process.equiv2.refl { from rfl, },
  case process.equiv2.symm : P Q _ ih { from symm ih },
  case process.equiv2.trans : P Q R _ _ pq qr { from trans pq qr },
  case process.equiv2.ξ_species : c A B eq {
    from process_immediate.equiv M ℓ conc (process.equiv.ξ_species eq),
  },
  case process.equiv2.ξ_parallel₁ : P P' Q eq ih {
    unfold process_immediate,
    rw [process_potential.equiv2 conc _ eq, ih],
    from rfl,
  },
  case process.equiv2.ξ_parallel₂ : P Q Q' eq ih {
    unfold process_immediate,
    rw [interaction_tensor.comm _ _,
        process_potential.equiv2 conc _ eq,
        interaction_tensor.comm _ _,
        ih],
    from rfl,
  },

  case process.equiv2.parallel_nil {
    from process_immediate.equiv M ℓ conc process.equiv.parallel_nil,
  },
  case process.equiv2.parallel_symm {
    from process_immediate.equiv M ℓ conc process.equiv.parallel_symm,
  },
  case process.equiv2.parallel_assoc {
    from process_immediate.equiv M ℓ conc process.equiv.parallel_assoc,
  },
  case process.equiv2.join {
    from process_immediate.equiv M ℓ conc process.equiv.join,
  },

  case process.equiv2.split : A B c {
    simp only [process_immediate],

    rw [process_potential.equiv2 conc _ process.equiv2.split,
        interaction_tensor.comm (process_potential M ℓ (c ◯ A |ₚ c ◯ B)) _],
    unfold_coes,
    rw [process_potential.equiv2 conc _ process.equiv2.split],
    simp only [process_potential],

    generalize eqPab : finset.sum (fintype.elems (transition.transition_from ℓ (A |ₛ B))) (immediate_process_space conc.to_embed) = Pab,
    generalize eqPa  : finset.sum (fintype.elems (transition.transition_from ℓ A)) (immediate_process_space conc.to_embed) = Pa,
    generalize eqPb  : finset.sum (fintype.elems (transition.transition_from ℓ B)) (immediate_process_space conc.to_embed) = Pb,

    suffices : Pab = Pa + Pb,
    {
      generalize : finset.sum (fintype.elems (transition.transition_from ℓ A)) potential_interaction_space = Da,
      generalize : finset.sum (fintype.elems (transition.transition_from ℓ B)) potential_interaction_space = Db,
      unfold_coes,

      simp only [interaction_tensor.left_distrib, interaction_tensor.right_distrib, smul_add],
      rw interaction_tensor.comm (c • Db) (c • Da),

      generalize : ½ • (c • Da) ⊘[conc.to_embed] (c • Da) = sa,
      generalize : ½ • (c • Db) ⊘[conc.to_embed] (c • Db) = sb,
      generalize : (c • Da) ⊘[conc.to_embed] (c • Db) = sab,
      generalize eSab : ½ • sab = sab2,

      calc  c • Pab + (sa + sab2 + (sab2 + sb))
          = c • Pab + (sa + (sb + (sab2 + sab2))) : by simp only [add_comm, add_left_comm]
      ... = c • Pab + (sa + (sb + sab)) : begin
              subst eSab,
              rw [← add_smul, ← half_ring.one_is_two_halves, one_smul],
            end
      ... = c • Pa + c • Pb + (sa + (sb + sab)) : by rw [this, smul_add]
      ... = c • Pa + sa + (c • Pb + sb) + sab : by abel,
    },


    subst eqPab, subst eqPa, subst eqPb,
    from process_immediate.split conc A B,
  }
end

lemma process_immediate.split'
  (A B : species ℍ ω (context.extend M.arity context.nil))
: finset.sum (fintype.elems (transition.transition_from ℓ (A |ₛ B))) (immediate_process_space conc.to_embed)
= finset.sum (fintype.elems (transition.transition_from ℓ A)) (immediate_process_space conc.to_embed)
+ finset.sum (fintype.elems (transition.transition_from ℓ B)) (immediate_process_space conc.to_embed)
:=
  calc  finset.sum (fintype.elems (transition.transition_from ℓ (A |ₛ B))) (immediate_process_space conc.to_embed)

      = finset.sum
          (finset.image sum.inl
              (finset.image sum.inl (fintype.elems (transition.transition_from ℓ A)) ∪
                  finset.image sum.inr (fintype.elems (transition.transition_from ℓ B))) ∪
            finset.image sum.inr (fintype.elems (com₁_of ℓ A B)))
          (λ (t : (transition.transition_from ℓ A ⊕ transition.transition_from ℓ B) ⊕ com₁_of ℓ A B),
            sum.elim (sum.elim (immediate_process_space conc.to_embed) (immediate_process_space conc.to_embed))
                (immediate_process_space conc.to_embed ∘ com₁_of.to_transition) t)
      : finset.sum_iso
          (λ t, immediate_process_space conc.to_embed t)
          (λ t, par_of.immediate_process_space conc t)
          (par_of.iso ℓ A B)
          (λ t, par_of.immediate_eq conc t)
          (fintype.elems _)
          ( finset.image sum.inl
              ( finset.image sum.inl (fintype.elems (transition.transition_from ℓ A))
              ∪ finset.image sum.inr (fintype.elems (transition.transition_from ℓ B)) )
            ∪ finset.image sum.inr (fintype.elems (com₁_of ℓ A B)) )
          (λ x _, par_of.complete ℓ A B _)
          (λ x _, fintype.complete _)

  ... = finset.sum (fintype.elems (transition.transition_from ℓ A)) (immediate_process_space conc.to_embed)
      + finset.sum (fintype.elems (transition.transition_from ℓ B)) (immediate_process_space conc.to_embed)
      + finset.sum (fintype.elems (com₁_of ℓ A B))
          (immediate_process_space conc.to_embed ∘ com₁_of.to_transition)
        : by rw [ ← finset.sum_sum_elim, ← finset.sum_sum_elim]

  ... = finset.sum (fintype.elems (transition.transition_from ℓ A)) (immediate_process_space conc.to_embed)
      + finset.sum (fintype.elems (transition.transition_from ℓ B)) (immediate_process_space conc.to_embed)
        : begin
          have : finset.sum (fintype.elems (com₁_of ℓ A B)) (immediate_process_space conc.to_embed ∘ com₁_of.to_transition)
               = (0 : process_space ℂ ℍ ω _)
              := finset.sum_eq_zero (λ t _, begin
                rcases t with ⟨ x, y, a, b, F, G, tf, tg ⟩,
                simp only [function.comp, com₁_of.to_transition, immediate_process_space],

                sorry,
              end),
          rw [this, add_zero],
        end

end cpi

#lint-
