import data.cpi.species.prime

namespace cpi
namespace species

variables {ℍ : Type} {ω : context}

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
    from calc  (A |ₛ B)
            ≈ (A |ₛ nil) : equiv.ξ_parallel₂ (depth_nil_rev (nat.eq_zero_of_add_eq_zero_left eq))
        ... ≈ A : equiv.parallel_nil₁
        ... ≈ nil : depth_nil_rev (nat.eq_zero_of_add_eq_zero_right eq)
  end
  | _ (ν(M) A) eq := begin
    unfold depth at eq,
    from calc  (ν(M) A)
            ≈ (ν(M) nil) : equiv.ξ_restriction M (depth_nil_rev eq)
        ... ≈ (ν(M) species.rename name.extend nil) : by simp only [rename.nil]
        ... ≈ nil : equiv.ν_drop₁ M
  end
  using_well_founded {
    rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, whole.sizeof ℍ ω kind.species x.1 x.2.1 ) ⟩ ],
    dec_tac := tactic.fst_dec_tac,
  }
end depth

/-- Construct a species from a prime decomposition of species. -/
def parallel.from_prime_decompose {Γ} : multiset (quotient (@prime_species.setoid ℍ ω Γ)) → quotient (@species.setoid ℍ ω Γ)
| ms := quot.lift_on ms
  (λ xs, parallel.quot.from_list (list.map prime_species.unwrap xs))
  (λ _ _ eq, parallel.quot.permute (list.perm_map prime_species.unwrap eq))

/-- A proof that a prime decomposition exists. -/
lemma has_prime_decompose :
  ∀ {Γ} (A : species ℍ ω Γ)
  , ∃ (As : multiset (quotient (@prime_species.setoid ℍ ω Γ)))
  , ⟦ A ⟧ = parallel.from_prime_decompose As
| Γ A :=
  match classical.dec (A ≈ nil) with
  | is_true is_nil :=
    ⟨ [], quot.sound is_nil ⟩
  | is_false non_nil :=
    match classical.dec (∃ B C, ¬ B ≈ nil ∧ ¬ C ≈ nil ∧ A ≈ (B |ₛ C)) with
    | is_true ⟨ B, C, nB, nC, eq ⟩ :=
        let lB : depth B < depth A := begin
            have : depth A = depth (B |ₛ C) := depth_eq eq, rw this, unfold depth,
            from lt_add_of_pos_right _ (nat.pos_of_ne_zero (λ x, nC (depth_nil_rev x)))
          end in
        let lC : depth C < depth A := begin
            have : depth A = depth (B |ₛ C) := depth_eq eq, rw this, unfold depth,
            from lt_add_of_pos_left _ (nat.pos_of_ne_zero (λ x, nB (depth_nil_rev x)))
          end in
        begin
          rcases has_prime_decompose B with ⟨ Bs, eqB ⟩,
          rcases has_prime_decompose C with ⟨ Cs, eqC ⟩,
          rcases quot.exists_rep Bs with ⟨ Bs, ⟨ _ ⟩ ⟩,
          rcases quot.exists_rep Cs with ⟨ Cs, ⟨ _ ⟩ ⟩,

          suffices : ⟦A⟧ = parallel.quot.from_list (list.map prime_species.unwrap (Bs ++ Cs)),
            from ⟨ ⟦ Bs ++ Cs ⟧, this ⟩,

          suffices : ⟦ B |ₛ C ⟧ = parallel.quot.from_list (list.map prime_species.unwrap Bs ++ list.map prime_species.unwrap Cs),
            rw list.map_append,
            from trans (quot.sound eq) this,

          suffices
            : parallel.quot.mk (parallel.from_prime_decompose ⟦Bs⟧) (parallel.from_prime_decompose ⟦Cs⟧)
            = parallel.quot.from_list (list.map prime_species.unwrap Bs ++ list.map prime_species.unwrap Cs),
            unfold quotient.mk at this, rw [← eqB, ← eqC] at this, from this,

          from symm (parallel.quot.from_append
            (list.map prime_species.unwrap Bs) (list.map prime_species.unwrap Cs)),
      end
    | is_false no_decompose :=
      let this : prime A := ⟨ non_nil, λ B C eq,
        match classical.dec (B ≈ nil), classical.dec (C ≈ nil) with
        | is_true is_nil, _ := or.inl is_nil
        | _, is_true is_nil := or.inr is_nil
        | is_false nnB, is_false nnC := false.elim (no_decompose ⟨ B, C, nnB, nnC, eq ⟩)
        end ⟩
      in ⟨ quotient.mk [ ⟦ ⟨ A, this ⟩ ⟧ ], by from rfl ⟩
    end
  end
using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, depth x.2 ) ⟩ ],
  dec_tac := tactic.fst_dec_tac,
}

end species
end cpi

#lint
