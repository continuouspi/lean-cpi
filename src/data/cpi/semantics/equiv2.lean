import data.cpi.semantics.basic

namespace cpi

variables {ℂ ℍ : Type} {ω : context} [half_ring ℂ] [species_equiv ℍ ω] [decidable_eq ℍ]
  {M : affinity ℍ}
  {ℓ : lookup ℍ ω (context.extend M.arity context.nil)}
local attribute [instance] concretion_equal transition.transition_eq

private def com₁_of {Γ : context} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ) :=
  (Σ' (x y : ℕ) (a b : name Γ)
      (F : concretion ℍ ω Γ x y) (G : concretion ℍ ω Γ y x)
  , transition A ℓ (#a) F × transition B ℓ (#b) G)

private constant com₁_of.fintype {Γ : context} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ)
  : fintype (com₁_of ℓ A B)
attribute [instance] com₁_of.fintype

private def com₁_of.to_transition {Γ : context} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ}
  : com₁_of ℓ A B → transition.transition_from ℓ (A |ₛ B)
| ⟨ x, y, a, b, F, G, tf, tg ⟩ := ⟨ _, _, _, transition.com₁ tf tg ⟩

private def par_of {Γ : context} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ) :=
  com₁_of ℓ A B ⊕ transition.transition_from ℓ A ⊕ transition.transition_from ℓ B

private def par_of.of_transition {Γ : context} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ} :
  ∀ {k} {α : label ℍ Γ k} {E}, (A |ₛ B) [ℓ, α]⟶ E → par_of ℓ A B
| _ _ _ (transition.com₁ tf tg) := sum.inl ⟨ _, _, _, _, _, _, tf, tg ⟩
| _ _ _ (transition.parₗ B t) := sum.inr (sum.inl ⟨ _, _, _, t ⟩)
| _ _ _ (transition.parᵣ A t) := sum.inr (sum.inr ⟨ _, _, _, t ⟩)

private def par_of.of_transition_from {Γ : context} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ} :
  transition.transition_from ℓ (A |ₛ B) → par_of ℓ A B
| ⟨ _, _, _, t ⟩ := par_of.of_transition t

private def par_of.parₗ {Γ : context} {ℓ : lookup ℍ ω Γ} (A B : species ℍ ω Γ)
  : transition.transition_from ℓ A → transition.transition_from ℓ (A |ₛ B)
| ⟨ k, α, E, t ⟩ := ⟨ k, α, _, transition.parₗ B t ⟩

private def par_of.parᵣ {Γ : context} {ℓ : lookup ℍ ω Γ} (A B : species ℍ ω Γ)
  : transition.transition_from ℓ B → transition.transition_from ℓ (A |ₛ B)
| ⟨ k, α, E, t ⟩ := ⟨ k, α, _, transition.parᵣ A t ⟩

private def par_of.to_transition {Γ : context} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ} :
  par_of ℓ A B → transition.transition_from ℓ (A |ₛ B)
| (sum.inl t) := com₁_of.to_transition t
| (sum.inr (sum.inl t)) := par_of.parₗ A B t
| (sum.inr (sum.inr t)) := par_of.parᵣ A B t

private def par_of.iso {Γ : context} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ)
  : transition.transition_from ℓ (A |ₛ B) ≃ par_of ℓ A B :=
  { to_fun := par_of.of_transition_from,
    inv_fun := par_of.to_transition,
    left_inv := λ x, begin
      rcases x with ⟨ k, α, E, t ⟩,
      cases t;
      simp only [par_of.of_transition, par_of.of_transition_from, par_of.to_transition, par_of.parₗ, par_of.parᵣ],
      case cpi.transition.com₁ : x y a b F G tf tg { from rfl },
    end,
    right_inv := λ x, begin
      rcases x with ⟨ x, y, a, b, F, G, tf, tg ⟩ | ⟨ k, α, E, t ⟩ | ⟨ k, α, E, t ⟩;
      simp only [par_of.of_transition, par_of.of_transition_from, par_of.to_transition,
                 com₁_of.to_transition, par_of.parₗ, par_of.parᵣ],
    end }

noncomputable def par_of.potential_interaction_space {Γ} {ℓ : lookup ℍ ω Γ} {A B : species ℍ ω Γ}
  : par_of ℓ A B
  → interaction_space ℂ ℍ ω Γ
| x := potential_interaction_space (par_of.to_transition x)

private lemma split_foo {Γ : context} (ℓ : lookup ℍ ω Γ) (A B : species ℍ ω Γ)
  : (fintype.elems (transition.transition_from ℓ A)).val
  = (multiset.partition_map id
      (multiset.partition_map par_of.of_transition_from (fintype.elems (transition.transition_from ℓ (A |ₛ B))).val).2).1
:= begin
  have h : ∀ (a : transition.transition_from ℓ A),
    a ∈ (multiset.partition_map id
      (multiset.partition_map par_of.of_transition_from (fintype.elems (transition.transition_from ℓ (A |ₛ B))).val).2).1,
    assume t,
    have x : par_of.parₗ A B t ∈ (fintype.elems (transition.transition_from ℓ (A |ₛ B))).val := fintype.complete _,
    rcases multiset.exists_cons_of_mem x with ⟨ all, h₂ ⟩,
    rw h₂,
    rcases quot.exists_rep all with ⟨ all, ⟨ _ ⟩ ⟩,
    squeeze_simp [multiset.partition_map, list.partition_map, quot.lift_on], unfold_coes,

    rcases t with ⟨ k, α, E, t ⟩,
    simp only [list.partition_map._match_1, list.partition_map, par_of.of_transition, par_of.of_transition_from, par_of.parₗ],
    generalize : (list.partition_map par_of.of_transition_from all) = all', rcases all' with ⟨ all₁, all₂ ⟩,
    simp only [prod.map, list.partition_map._match_1, list.partition_map, id],
    generalize : list.partition_map id all₂ = all₂', rcases all₂' with ⟨ all₃, all₄ ⟩,
    simp only [prod.map],

    simp only [list.mem_cons_iff, multiset.mem_coe, multiset.quot_mk_to_coe''],
    from or.inl rfl,
  -- refine multiset.nodup_ext _,
  -- have h : ∀ (a : α), a ∈ s ↔ a ∈ t
end


lemma process_potential.split [add_monoid ℍ]
  (conc : distrib_embedding ℍ ℂ (+) (+))
  (ξ : interaction_space ℂ ℍ ω (context.extend (M.arity) context.nil))
  (P Q : process ℂ ℍ ω (context.extend (M.arity) context.nil))
  (A B : species ℍ ω (context.extend (M.arity) context.nil))
  (c : ℂ)
: process_potential M ℓ (c ◯ (A |ₛ B)) ⊘[conc.to_embed] ξ
= process_potential M ℓ (c ◯ A |ₚ c ◯ B) ⊘[↑conc] ξ := begin
  simp only [process_potential, interaction_tensor.left_distrib],
  unfold_coes,

  suffices
    : multiset.sum_map potential_interaction_space ((fintype.elems (transition.transition_from ℓ (A |ₛ B))).val)
    = multiset.sum_map potential_interaction_space ((fintype.elems (transition.transition_from ℓ A)).val)
    + multiset.sum_map potential_interaction_space ((fintype.elems (transition.transition_from ℓ B)).val),
    rw [← interaction_tensor.left_distrib, ← smul_add, ← this],

  from calc  multiset.sum_map potential_interaction_space ((fintype.elems (transition.transition_from ℓ (A |ₛ B))).val)
           = multiset.sum_map (par_of.potential_interaction_space ∘ par_of.of_transition_from)
             (fintype.elems (transition.transition_from ℓ (A |ₛ B))).val
             : begin
                have : @potential_interaction_space ℂ ℍ ω _ _ _ _ ℓ (A |ₛ B) = (par_of.potential_interaction_space ∘ par_of.of_transition_from),
                { apply funext, assume x,
                  simp only [function.comp, par_of.potential_interaction_space],
                  suffices : par_of.to_transition (par_of.of_transition_from x) = x, { rw this },
                  from (par_of.iso ℓ A B).left_inv x,
                },
                rw ← this,
             end

        ... = multiset.sum_map (@potential_interaction_space ℂ ℍ ω _ _ _ _ ℓ (A |ₛ B))
              (multiset.map par_of.to_transition
               (multiset.map par_of.of_transition_from (fintype.elems (transition.transition_from ℓ (A |ₛ B))).val))
           : by simp only [multiset.sum_map, function.comp_app, multiset.map_map, par_of.potential_interaction_space]

       ... = multiset.sum_map (potential_interaction_space ∘ par_of.parₗ A B) ((fintype.elems (transition.transition_from ℓ A)).val)
           + multiset.sum_map (potential_interaction_space ∘ par_of.parᵣ A B) ((fintype.elems (transition.transition_from ℓ B)).val)
           + multiset.sum_map (potential_interaction_space ∘ com₁_of.to_transition) ((fintype.elems (com₁_of ℓ A B)).val)
           : begin
              rw ← multiset.partition_map_append,
              simp only [function.comp, multiset.map_map, multiset.map_add, par_of.to_transition],
              rw [← multiset.map_id ((multiset.partition_map par_of.of_transition_from _).snd),
                  ← multiset.partition_map_append],
              simp only [function.comp, multiset.map_map, multiset.map_add, par_of.to_transition],

              simp only [multiset.sum_map, multiset.map_add],
              have : ∀ (xs ys : multiset (interaction_space ℂ ℍ ω (context.extend (M.arity) context.nil)))
                   , multiset.fold (+) 0 (xs + ys)
                   = multiset.fold (+) (0 + 0) (xs + ys)
                   := λ xs ys, by rw add_zero (0 : interaction_space ℂ ℍ ω _),
              simp only [this, multiset.fold_add, multiset.map_map, function.comp],
              sorry,
           end

       ... = multiset.sum_map potential_interaction_space ((fintype.elems (transition.transition_from ℓ A)).val)
           + multiset.sum_map potential_interaction_space ((fintype.elems (transition.transition_from ℓ B)).val)
           : begin
            sorry,
           end,
end

/-
lemma process_potential.equiv2 [add_monoid ℍ]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
    (conc : distrib_embedding ℍ ℂ (+) (+))
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
    from process_potential.split conc ξ P Q A B c,
    -- have : ∀ (x : transition.transition_from ℓ (A |ₛ B)),
    --   sum (Σ' (x y : ℕ) (a b : name (context.extend M.arity context.nil))
    --           (F : concretion ℍ ω (context.extend M.arity context.nil) x y) (G : concretion ℍ ω (context.extend M.arity context.nil) y x)
    --       , transition A ℓ (#a) F × transition B ℓ (#b) G)
    --   (sum (transition.transition_from ℓ A)
    --         (transition.transition_from ℓ B)),
    -- {
    --   assume x,
    --   rcases x with ⟨ k, α, E, t ⟩,
    --   cases t,
    --   case transition.com₁ : x y a b F G tf tg {
    --     unfold potential_interaction_space,
    --     refine psum.inl _,
    --     from ℂ, assumption, apply_instance, from rfl,
    --   },
    --   case transition.parₗ : E t' { from psum.inr (sum.inl ⟨ k, α, E, t' ⟩) },
    --   case transition.parᵣ : E t' { from psum.inr (sum.inr ⟨ k, α, E, t' ⟩) },
    -- },

    -- simp only [multiset.sum_map],
    -- rw ← multiset.fold_add has_add.add,
    -- simp only [add_zero],
    -- rw ← multiset.map_add potential_interaction_space,
    -- TODO: Show isomorphism between the two, then use multiset.map_ido
  },
end

lemma process_immediate.equiv2 [add_monoid ℍ]
    (M : affinity ℍ) (ℓ : lookup ℍ ω (context.extend M.arity context.nil))
    (conc : distrib_embedding ℍ ℂ (+) (+))
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
    rw [process_potential.equiv2 M ℓ conc _ eq, ih],
    from rfl,
  },
  case process.equiv2.ξ_parallel₂ : P Q Q' eq ih {
    unfold process_immediate,
    rw [interaction_tensor.comm _ _,
        process_potential.equiv2 M ℓ conc _ eq,
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

    generalize eqPab : multiset.sum_map (immediate_process_space conc.to_embed) ((fintype.elems (transition.transition_from ℓ (A |ₛ B))).val) = Pab,
    generalize eqPa  : multiset.sum_map (immediate_process_space conc.to_embed) ((fintype.elems (transition.transition_from ℓ A)).val) = Pa,
    generalize eqPb  : multiset.sum_map (immediate_process_space conc.to_embed) ((fintype.elems (transition.transition_from ℓ B)).val) = Pb,

    rw [process_potential.equiv2 M ℓ conc _ process.equiv2.split,
        interaction_tensor.comm (process_potential M ℓ (c ◯ A |ₚ c ◯ B)) _],
    unfold_coes,
    rw [process_potential.equiv2 M ℓ conc _ process.equiv2.split],
    simp only [process_potential],

    suffices : Pab = Pa + Pb,
    {
      generalize : multiset.sum_map potential_interaction_space ((fintype.elems (transition.transition_from ℓ A)).val) = Da,
      generalize : multiset.sum_map potential_interaction_space ((fintype.elems (transition.transition_from ℓ B)).val) = Db,
      unfold_coes,

      simp only [interaction_tensor.left_distrib, interaction_tensor.right_distrib, smul_add],
      rw interaction_tensor.comm (c • Db) (c • Da),

      generalize : ½ • (c • Da) ⊘[conc.to_embed] (c • Da) = sa,
      generalize : ½ • (c • Db) ⊘[conc.to_embed] (c • Db) = sb,
      generalize : (c • Da) ⊘[conc.to_embed] (c • Db) = sab,
      generalize eSab : ½ • sab = sab2,

      from calc  c • Pab + (sa + sab2 + (sab2 + sb))
               = c • Pab + (sa + (sb + (sab2 + sab2))) : by simp only [add_comm, add_left_comm]
           ... = c • Pab + (sa + (sb + sab)) : begin
                  subst eSab,
                  rw [← fin_fn.add_smul, ← half_ring.one_is_two_halves, one_smul],
               end
           ... = c • Pa + c • Pb + (sa + (sb + sab)) : by rw [this, smul_add]
           ... = c • Pa + sa + (c • Pb + sb) + sab : by abel,
    },


    subst eqPab, subst eqPa, subst eqPb,
    sorry,
  }
end
-/
end cpi

#lint-
