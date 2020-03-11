import data.cpi.semantics.basic

namespace cpi

variables {ℂ ℍ : Type} {ω : context} [half_ring ℂ] [cpi_equiv_prop ℍ ω] [add_monoid ℍ] [decidable_eq ℂ]
  {M : affinity ℍ}
  {ℓ : lookup ℍ ω (context.extend M.arity context.nil)}
  (conc : distrib_embedding ℍ ℂ (+) (+))

axiom process_potential.split
  (A B : species ℍ ω (context.extend (M.arity) context.nil))
: ( finset.sum (fintype.elems (transition.transition_from ℓ (A |ₛ B))) potential_interaction_space
  : interaction_space ℂ ℍ ω (context.extend M.arity context.nil) )
= finset.sum (fintype.elems (transition.transition_from ℓ A)) potential_interaction_space
+ finset.sum (fintype.elems (transition.transition_from ℓ B)) potential_interaction_space

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
    rw [← interaction_tensor.left_distrib, ← smul_add,
        ← process_potential.split A B],
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

end cpi

#lint-
