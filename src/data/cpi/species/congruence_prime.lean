import data.cpi.species.congruence data.cpi.species.prime

namespace cpi
namespace species
namespace equiv
variables {ℍ : Type} {ω : context}
open_locale congruence

section depth
  private def depth : ∀ {Γ}, species ℍ ω Γ → ℕ
  | _ nil := 0
  | _ (apply _ _) := 1
  | _ (Σ# _) := 1
  | _ (A |ₛ B) := depth A + depth B
  | Γ (ν(_) A) := depth A
  using_well_founded {
    rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, whole.sizeof ℍ ω kind.species x.fst x.snd ) ⟩ ],
    dec_tac := tactic.fst_dec_tac,
  }

  private lemma depth_rename : ∀ {Γ Δ} (ρ : name Γ → name Δ) (A : species ℍ ω Γ), depth (rename ρ A) = depth A
  | _ _ ρ nil := by simp only [rename.nil, depth]
  | _ _ ρ (apply _ _) := by simp only [rename.invoke, depth]
  | _ _ ρ (Σ# _) := by simp only [rename.choice, depth]
  | _ _ ρ (A |ₛ B) := begin
    simp only [rename.parallel, depth],
    rw [depth_rename ρ A, depth_rename ρ B],
  end
  | _ _ ρ (ν(_) A) := begin
    simp only [rename.restriction, depth],
    from depth_rename (name.ext ρ) A,
  end
  using_well_founded {
    rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, whole.sizeof ℍ ω kind.species x.1 x.2.2.2 ) ⟩ ],
    dec_tac := tactic.fst_dec_tac,
  }

  private lemma depth_eq : ∀ {Γ} {A B : species ℍ ω Γ}, A ≈ B → depth A = depth B
  | Γ A B ⟨ eq ⟩ := begin
    induction eq,
    case equivalent.refl { from rfl },
    case equivalent.trans : _ A' B' C' ab bc ihab ihbc { from trans ihab ihbc },
    case equivalent.ξ_parallel₁ : _ A' A'' B eq ih { unfold depth, rw ih },
    case equivalent.ξ_parallel₂ : _ A B' B' eq ih { unfold depth, rw ih },
    case equivalent.ξ_restriction : _ M A A' eq ih { unfold depth, rw ih },
    all_goals { repeat { unfold depth <|> simp only [add_zero, zero_add, add_comm, add_assoc, depth_rename] } },
  end

  private lemma depth_nil : ∀ {Γ} {A : species ℍ ω Γ}, A ≈ nil → depth A = 0
  | Γ A eq := by { have eq := depth_eq eq, unfold depth at eq, from eq }

  private lemma depth_nil_rev : ∀ {Γ} {A : species ℍ ω Γ}, depth A = 0 → A ≈ nil
  | _ nil eq := refl _
  | _ (apply _ _) eq := by { unfold depth at eq, contradiction }
  | _ (Σ# _) eq:= by { unfold depth at eq, contradiction }
  | _ (A |ₛ B) eq := begin
    unfold depth at eq,
    calc  (A |ₛ B)
        ≈ (A |ₛ nil) : equiv.ξ_parallel₂ (depth_nil_rev (nat.eq_zero_of_add_eq_zero_left eq))
    ... ≈ A : equiv.parallel_nil₁
    ... ≈ nil : depth_nil_rev (nat.eq_zero_of_add_eq_zero_right eq)
  end
  | _ (ν(M) A) eq := begin
    unfold depth at eq,
    calc  (ν(M) A)
        ≈ (ν(M) nil) : equiv.ξ_restriction M (depth_nil_rev eq)
    ... ≈ (ν(M) species.rename name.extend nil) : by simp only [rename.nil]
    ... ≈ nil : equiv.ν_drop₁ M
  end
  using_well_founded {
    rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, whole.sizeof ℍ ω kind.species x.1 x.2.1 ) ⟩ ],
    dec_tac := tactic.fst_dec_tac,
  }
end depth

open_locale classical

/-- A procecure to compute the prime decomposition of a species using classical
    logic. This is sound, but non-computable. -/
noncomputable def do_prime_decompose {Γ} :
  ∀ (A : species ℍ ω Γ)
  , Σ' (As : list (prime_species ℍ ω Γ))
    , A ≈ parallel.from_list (list.map subtype.val As)
| A :=
  if is_nil : A ≈ nil then
    ⟨ [], is_nil ⟩
  else if has_decomp : ∃ B C, ¬ B ≈ nil ∧ ¬ C ≈ nil ∧ A ≈ (B |ₛ C) then
    let B := classical.some has_decomp in
    let C := classical.some (classical.some_spec has_decomp) in
    have h : ¬B ≈ nil ∧ ¬C ≈ nil ∧ A ≈ (B |ₛ C) := classical.some_spec (classical.some_spec has_decomp),
    have lB : depth B < depth A := begin
        have : depth A = depth (B |ₛ C) := depth_eq h.2.2, rw this, unfold depth,
        from lt_add_of_pos_right _ (nat.pos_of_ne_zero (λ x, h.2.1 (depth_nil_rev x)))
      end,
    have lC : depth C < depth A := begin
        have : depth A = depth (B |ₛ C) := depth_eq h.2.2, rw this, unfold depth,
        from lt_add_of_pos_left _ (nat.pos_of_ne_zero (λ x, h.1 (depth_nil_rev x)))
      end,
    let Bs := do_prime_decompose B in
    let Cs := do_prime_decompose C in
    suffices this : A ≈ parallel.from_list (list.map subtype.val (Bs.1 ++ Cs.1)),
      from ⟨ Bs.1 ++ Cs.1, this ⟩,
    calc  A
        ≈ (B |ₛ C) : h.2.2
    ... ≈ (parallel.from_list (list.map subtype.val Bs.1) |ₛ parallel.from_list (list.map subtype.val Cs.1))
        : trans (equiv.ξ_parallel₁ Bs.2) (equiv.ξ_parallel₂ Cs.2)
    ... ≈ parallel.from_list (list.map subtype.val Bs.1 ++ list.map subtype.val Cs.1)
          : (parallel.from_append _ _).symm
    ... ≈ parallel.from_list (list.map subtype.val (Bs.1 ++ Cs.1)) : by rw list.map_append
  else
    suffices this : prime A, from ⟨ [ ⟨ A, this ⟩ ], refl _ ⟩,
    ⟨ is_nil, λ B C eq,
      if nilB : B ≈ nil then or.inl nilB else
      if nilC : C ≈ nil then or.inr nilC else
      false.elim (has_decomp ⟨ B, C, nilB, nilC, eq ⟩) ⟩
using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf depth ⟩ ],
  dec_tac := tactic.fst_dec_tac',
}

/-- Decompose a species into its constituent primes. -/
noncomputable def prime_decompose {Γ} (A : species ℍ ω Γ) : multiset (prime_species ℍ ω Γ)
  := ⟦ (do_prime_decompose A).1 ⟧

lemma prime_decompose_nil {Γ} : prime_decompose (@nil ℍ ω Γ) = 0 := begin
  unfold prime_decompose do_prime_decompose,
  simpa only [dif_pos (refl nil)],
end

lemma prime_decompose_prime {Γ} : ∀ (A : prime_species ℍ ω Γ), prime_decompose A.val = [ A ]
| ⟨ A, ⟨ n_nil, n_decompose ⟩ ⟩ := begin
  have n_exist : ¬ ∃ (B C : whole ℍ ω kind.species Γ), ¬B ≈ nil ∧ ¬C ≈ nil ∧ A ≈ (B |ₛ C),
  { rintros ⟨ B, C, nB, nC, r ⟩, from or.elim (n_decompose B C r) nB nC },
  unfold prime_decompose do_prime_decompose,
  simpa only [dif_neg n_nil, dif_neg n_exist],
end

end equiv
end species
end cpi

#lint-
