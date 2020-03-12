import data.cpi.semantics.basic

namespace cpi

variables {ℂ ℍ : Type} {ω : context} [half_ring ℂ] [cpi_equiv_prop ℍ ω] [add_monoid ℍ] [decidable_eq ℂ]
  {M : affinity ℍ}
  {ℓ : lookup ℍ ω (context.extend M.arity context.nil)}
  (conc : distrib_embedding ℍ ℂ (+) (+))

axiom process_potential.split
  (A B : species ℍ ω (context.extend (M.arity) context.nil))
  (ξ : interaction_space ℂ ℍ ω (context.extend M.arity context.nil))
: finset.sum (fintype.elems (transition.transition_from ℓ (A |ₛ B))) potential_interaction_space
  ⊘[conc.to_embed] ξ
= ( finset.sum (fintype.elems (transition.transition_from ℓ A)) potential_interaction_space
  + finset.sum (fintype.elems (transition.transition_from ℓ B)) potential_interaction_space )
  ⊘[conc.to_embed] ξ

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

private def com₁_of {Γ} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ) :=
  (Σ' (x y : ℕ) (a b : name Γ)
      (F : concretion ℍ ω Γ x y) (G : concretion ℍ ω Γ y x)
  , transition A ℓ (#a) (production.concretion F) × transition B ℓ (#b) (production.concretion G))

private constant com₁_of.fintype {Γ : context} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ)
  : fintype (com₁_of ℓ A B)
attribute [instance] com₁_of.fintype

private def com₁_of.to_transition {Γ : context} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ}
  : com₁_of ℓ A B → transition.transition_from ℓ (A |ₛ B)
| ⟨ x, y, a, b, F, G, tf, tg ⟩ := ⟨ _, _, _, transition.com₁ tf tg ⟩

lemma com₁_of.interaction_zero {Γ} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ} :
  ∀ (t : com₁_of ℓ A B)
  , potential_interaction_space (com₁_of.to_transition t)
  = (0 : interaction_space ℂ ℍ ω Γ)
| ⟨ x, y, a, b, F, G, tf, tg ⟩ := rfl

private def par_of {Γ : context} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ) :=
  (transition.transition_from ℓ A ⊕ transition.transition_from ℓ B) ⊕ com₁_of ℓ A B

private def par_of.of_transition {Γ : context} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ} :
  ∀ {k} {α : label ℍ Γ k} {E}, (A |ₛ B) [ℓ, α]⟶ E → par_of ℓ A B
| _ _ _ (transition.parL_species _ t) := sum.inl (sum.inl ⟨ _, _, _, t ⟩)
| _ _ _ (transition.parL_concretion _ t) := sum.inl (sum.inl ⟨ _, _, _, t ⟩)
| _ _ _ (transition.parR_species _ t) := sum.inl (sum.inr ⟨ _, _, _, t ⟩)
| _ _ _ (transition.parR_concretion _ t) := sum.inl (sum.inr ⟨ _, _, _, t ⟩)
| _ _ _ (transition.com₁ tf tg) := sum.inr ⟨ _, _, _, _, _, _, tf, tg ⟩

private def par_of.of_transition_from {Γ : context} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ} :
  transition.transition_from ℓ (A |ₛ B) → par_of ℓ A B
| ⟨ _, _, _, t ⟩ := par_of.of_transition t

private def par_of.parL {Γ : context} {ℓ : lookup ℍ ω Γ} (A B : species ℍ ω Γ)
  : transition.transition_from ℓ A → transition.transition_from ℓ (A |ₛ B)
| ⟨ _, α, production.species E, t ⟩ := ⟨ _, α, _, transition.parL_species B t ⟩
| ⟨ _, α, production.concretion E, t ⟩ := ⟨ _, α, _, transition.parL_concretion B t ⟩

private def par_of.parR {Γ : context} {ℓ : lookup ℍ ω Γ} (A B : species ℍ ω Γ)
  : transition.transition_from ℓ B → transition.transition_from ℓ (A |ₛ B)
| ⟨ _, α, production.species E, t ⟩ := ⟨ _, α, _, transition.parR_species A t ⟩
| ⟨ _, α, production.concretion E, t ⟩ := ⟨ _, α, _, transition.parR_concretion A t ⟩

private def par_of.to_transition {Γ : context} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ} :
  par_of ℓ A B → transition.transition_from ℓ (A |ₛ B)
  := sum.elim (sum.elim (par_of.parL A B) (par_of.parR A B)) com₁_of.to_transition

private def par_of.iso {Γ : context} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ)
  : transition.transition_from ℓ (A |ₛ B) ≃ par_of ℓ A B :=
  { to_fun := par_of.of_transition_from,
    inv_fun := par_of.to_transition,
    left_inv := λ x, begin
      rcases x with ⟨ k, α, E, t ⟩,
      cases t;
      simp only [par_of.of_transition_from, par_of.of_transition, par_of.to_transition, sum.elim, par_of.parL, par_of.parR],
      from rfl,
    end,
    right_inv := λ x, begin
      rcases x with ⟨ ⟨ k, α, ⟨ E | E ⟩, t ⟩ | ⟨ k, α, ⟨ E | E ⟩, t ⟩ ⟩ | ⟨ x, y, a, b, F, G, tf, tg ⟩;
      simp only [par_of.of_transition, par_of.of_transition_from, par_of.to_transition,
                 com₁_of.to_transition, par_of.parL, par_of.parR, sum.elim],
    end }

private lemma par_of.immediate_eq {A B : species ℍ ω (context.extend M.arity context.nil)} :
  ∀ (x : par_of ℓ A B)
  , immediate_process_space conc.to_embed (par_of.to_transition x)
  = (sum.elim (sum.elim (immediate_process_space conc.to_embed) (immediate_process_space conc.to_embed))
          ((immediate_process_space conc.to_embed) ∘ com₁_of.to_transition)) x
| (sum.inl (sum.inl ⟨ k, α, E, t ⟩)) := begin
  cases E,
  case production.concretion : b y E { cases α, from rfl },
  case production.species : C {
    simp only [par_of.to_transition, sum.elim, par_of.parL],
    have proc_eq : to_process_space ⟦C |ₛ B⟧ - to_process_space ⟦A |ₛ B⟧
                 = to_process_space ⟦C⟧ - to_process_space ⟦A⟧,
    {
      calc  (to_process_space ⟦C |ₛ B⟧ : process_space ℂ ℍ ω _) - to_process_space ⟦A |ₛ B⟧
          = to_process_space ⟦C⟧ + to_process_space ⟦B⟧ - (to_process_space ⟦A⟧ + to_process_space ⟦B⟧)
            : by rw [to_process_space.parallel C B, to_process_space.parallel A B]
      ... = to_process_space ⟦C⟧ - to_process_space ⟦A⟧ : by abel
    },

    cases α; simp only [immediate_process_space, proc_eq],
  }
end
| (sum.inl (sum.inr ⟨ k, α, E, t ⟩)) := begin
  cases E,
  case production.concretion : b y E { cases α, from rfl },
  case production.species : C {
    simp only [par_of.to_transition, sum.elim, par_of.parR],
    have proc_eq : to_process_space ⟦A |ₛ C⟧ - to_process_space ⟦A |ₛ B⟧
      = to_process_space ⟦C⟧ - to_process_space ⟦B⟧,
    {
      calc  (to_process_space ⟦A |ₛ C⟧ : process_space ℂ ℍ ω _) - to_process_space ⟦A |ₛ B⟧
          = to_process_space ⟦A⟧ + to_process_space ⟦C⟧ - (to_process_space ⟦A⟧ + to_process_space ⟦B⟧)
            : by rw [to_process_space.parallel A C, to_process_space.parallel A B]
      ... = to_process_space ⟦C⟧ - to_process_space ⟦B⟧ : by abel
    },

    cases α; simp only [immediate_process_space, proc_eq],
  }
end
| (sum.inr t) := rfl

private lemma par_of.potential_eq
  {A B : species ℍ ω (context.extend M.arity context.nil)}
  (ξ : interaction_space ℂ ℍ ω (context.extend M.arity context.nil)) :
  ∀ (x : par_of ℓ A B)
  , potential_interaction_space (par_of.to_transition x)
    ⊘[conc.to_embed] ξ
  = sum.elim
      (sum.elim potential_interaction_space potential_interaction_space)
      (potential_interaction_space ∘ com₁_of.to_transition) x
    ⊘[conc.to_embed] ξ
| (sum.inl (sum.inl ⟨ k, α, E, t ⟩)) := begin
  simp only [par_of.to_transition, sum.elim],
  cases E,
  case production.species : C { cases α; from rfl },
  case production.concretion : b y F {
    cases α with _ a, simp only [par_of.parL, potential_interaction_space],
    from interaction_tensor.parallel₁ A B F a 1 ξ,
  }
end
| (sum.inl (sum.inr ⟨ k, α, E, t ⟩)) := begin
  simp only [par_of.to_transition, sum.elim],
  cases E,
  case production.species : C { cases α; from rfl },
  case production.concretion : b y F {
    cases α with _ a, simp only [par_of.parR, potential_interaction_space],
    from interaction_tensor.parallel₂ A B F a 1 ξ,
  }
end
| (sum.inr t) := rfl

end cpi

#lint-
