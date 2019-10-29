import data.cpi.species.prime
import algebra.pi_instances

set_option profiler true
set_option profiler.threshold 0.5

namespace cpi
namespace species
variable {ω : context}

section depth
  private def depth : ∀ {Γ}, species ω Γ → ℕ
  | _ nil := 0
  | _ (apply _ _) := 1
  | _ (Σ# _) := 1
  | _ (A |ₛ B) := depth A + depth B
  | Γ (ν(_) A) := depth A
  using_well_founded {
    rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, whole.sizeof ω kind.species x.fst x.snd ) ⟩ ],
    dec_tac := tactic.fst_dec_tac,
  }

  private lemma depth_rename : ∀ {Γ Δ} (ρ : name Γ → name Δ) (A : species ω Γ), depth (rename ρ A) = depth A
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
    rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, whole.sizeof ω kind.species x.1 x.2.2.2 ) ⟩ ],
    dec_tac := tactic.fst_dec_tac,
  }

  private lemma depth_eq : ∀ {Γ} {A B : species ω Γ}, A ≈ B → depth A = depth B
  | Γ A B eq := begin
    induction eq,
    case equiv.refl { from rfl },
    case equiv.trans : _ A' B' C' ab bc ihab ihbc { from trans ihab ihbc },
    case equiv.ξ_parallel₁ : _ A' A'' B eq ih { unfold depth, rw ih },
    case equiv.ξ_parallel₂ : _ A B' B' eq ih { unfold depth, rw ih },
    case equiv.ξ_restriction : _ M A A' eq ih { unfold depth, rw ih },
    all_goals { repeat { unfold depth <|> simp only [add_zero, zero_add, add_comm, add_assoc, depth_rename] } },
  end

  private lemma depth_nil : ∀ {Γ} {A : species ω Γ}, A ≈ nil → depth A = 0
  | Γ A eq := by { have eq := depth_eq eq, unfold depth at eq, from eq }

  private lemma depth_nil_rev : ∀ {Γ} {A : species ω Γ}, depth A = 0 → A ≈ nil
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
    rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, whole.sizeof ω kind.species x.1 x.2.1 ) ⟩ ],
    dec_tac := tactic.fst_dec_tac,
  }
end depth

/-- Convert a multiset back into a species. -/
def parallel.from_multiset {Γ} : multiset (species ω Γ) → quotient (@species.setoid ω Γ)
| ms := quot.lift
    (λ x, ⟦ parallel.from_list x ⟧)
    (λ _ _ p, quotient.sound (parallel.permute p))
    ms

/-- A proof that a prime decomposition exists. -/
lemma has_prime_decompose :
  ∀ {Γ} (A : species ω Γ)
  , ∃ (As : multiset (species ω Γ))
  , ⟦ A ⟧ = parallel.from_multiset As ∧ ∀ x ∈ As, prime x
| Γ A :=
  match classical.dec (A ≈ nil) with
  | is_true is_nil :=
    ⟨ [], quot.sound is_nil, λ x mem, by cases mem ⟩
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
          rcases has_prime_decompose B with ⟨ Bs, eqB, pb ⟩,
          rcases has_prime_decompose C with ⟨ Cs, eqC, pc ⟩,
          clear lB lC,

          rcases quot.exists_rep Bs with ⟨ Bs, ⟨ _ ⟩ ⟩,
          rcases quot.exists_rep Cs with ⟨ Cs, ⟨ _ ⟩ ⟩,

          suffices : A ≈ parallel.from_list (Bs ++ Cs),
            from ⟨ quot.mk setoid.r Bs + quot.mk setoid.r Cs, quot.sound this,
                  λ x mem, or.elim (list.mem_append.mp mem) (pb x) (pc x) ⟩,
          from calc  A
                   ≈ (B |ₛ C) : eq
               ... ≈ (parallel.from_list Bs |ₛ C) : equiv.ξ_parallel₁ (quotient.exact eqB)
               ... ≈ (parallel.from_list Bs |ₛ parallel.from_list Cs) : equiv.ξ_parallel₂ (quotient.exact eqC)
               ... ≈ parallel.from_list (Bs ++ Cs) : symm (species.parallel.from_append Bs Cs)
      end
    | is_false no_decompose :=
        ⟨ [A], refl _,
          λ x mem, begin
            cases ((or_false _).mp mem),
            from ⟨ non_nil, λ B C eq,
              match classical.dec (B ≈ nil), classical.dec (C ≈ nil) with
              | is_true is_nil, _ := or.inl is_nil
              | _, is_true is_nil := or.inr is_nil
              | is_false nnB, is_false nnC := false.elim (no_decompose ⟨ B, C, nnB, nnC, eq ⟩)
              end ⟩
          end ⟩
    end
  end
using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, depth x.2 ) ⟩ ],
  dec_tac := tactic.fst_dec_tac,
}

def process_space (ω Γ : context) := prime_species ω Γ → ℝ

instance process_space.add_comm_group {ω Γ} : add_comm_group (process_space ω Γ)
  := by { unfold process_space, apply_instance }

/-- Convert a single prime species into a process space. This returns one when
    the process is present, and 0 otherwise. -/
private noncomputable def to_process_space_of {Γ} (A : prime_species ω Γ) : process_space ω Γ
| ⟨ B, p' ⟩ :=
  match classical.dec (A.val ≈ B) with
  | is_true _ := 1
  | is_false _ := 0
  end

/-- Convert a species into a process space. This computes the prime
    decomposition, and then converts it to a process space. -/
noncomputable def to_process_space {Γ} (A : multiset (prime_species ω Γ)) : process_space ω Γ
  := quot.lift_on A
      (list.foldr (λ B s, to_process_space_of B + s) 0)
      (λ a b p, begin
        induction p,
        case list.perm.nil { from rfl },
        case list.perm.skip : A l₁ l₂ eq ih { unfold list.foldr, rw ih },
        case list.perm.swap : A B l { simp only [add_comm, list.foldr, add_left_comm] },
        case list.perm.trans : l₁ l₂ l₃ ab bc ihab ihbc { from trans ihab ihbc },
      end)

end species
end cpi

#lint
