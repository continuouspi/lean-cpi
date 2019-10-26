import data.fin.pi_order data.real.non_neg data.option.order data.pand

set_option profiler true
set_option profiler.threshold 0.5

namespace cpi

/-- An affinity network.

    This is composed of $arity$ names, and a partial function `f' which defines
    the affinities between elements of this matrix.
-/
@[derive decidable_eq]
structure affinity := intro ::
  (arity : ℕ)
  (f : fin arity → fin arity → option ℝ≥0)
  (symm : ∀ x y, f x y = f y x)

/- Just show that affinity networks form a decidable linear order. -/
section ordering
  def affinity.le : affinity → affinity → Prop
  | ⟨ a, f, sf ⟩ ⟨ b, g, sg ⟩ :=
    a < b ∨ (Σ∧ (x : a = b), cast (congr_arg (λ x, fin x → fin x → option ℝ≥0) x) f ≤ g)

  protected theorem affinity.le_refl : ∀ M, affinity.le M M
  | ⟨ a, f, _ ⟩ := or.inr ⟨ rfl, le_refl f ⟩

  protected theorem affinity.le_trans :
    ∀ M N O, affinity.le M N → affinity.le N O → affinity.le M O
  | ⟨ a, f, sf ⟩ ⟨ b, g, sg ⟩ ⟨ c, h, sh ⟩ (or.inl lt) (or.inl lt')
    := or.inl (lt_trans lt lt')
  | ⟨ a, f, sf ⟩ ⟨ _, g, sg ⟩ ⟨ _, h, sh ⟩ (or.inl lt) (or.inr ⟨ eq.refl b, le ⟩)
    := or.inl lt
  | ⟨ _, f, sf ⟩ ⟨ _, g, sg ⟩ ⟨ c, h, sh ⟩ (or.inr ⟨ eq.refl a, le ⟩) (or.inl lt)
    := or.inl lt
  | ⟨ _, f, sf ⟩ ⟨ _, g, sg ⟩ ⟨ _, h, sh ⟩ (or.inr ⟨ eq.refl _, le ⟩) (or.inr ⟨ eq.refl a, le' ⟩)
    := or.inr ⟨ rfl, le_trans le le' ⟩

  protected theorem affinity.le_antisymm :
    ∀ M N, affinity.le M N → affinity.le N M → M = N
  | ⟨ a, f, sf ⟩ ⟨ b, g, sg ⟩ (or.inl lt) (or.inl lt')
    := false.elim (lt_asymm lt lt')
  | ⟨ a, f, sf ⟩ ⟨ _, g, sg ⟩ (or.inl lt) (or.inr ⟨ eq.refl b, le ⟩)
    := false.elim (lt_irrefl _ lt)
  | ⟨ _, f, sf ⟩ ⟨ _, g, sg ⟩ (or.inr ⟨ eq.refl a, le ⟩) (or.inl lt)
    := false.elim (lt_irrefl _ lt)
  | ⟨ _, f, sf ⟩ ⟨ _, g, sg ⟩ (or.inr ⟨ eq.refl _, le ⟩) (or.inr ⟨ eq.refl a, le' ⟩)
    := by { simp, from le_antisymm le le' }

  protected theorem affinity.le_total :
    ∀ M N, affinity.le M N ∨ affinity.le N M
  | ⟨ a, f, _ ⟩ ⟨ b, g, _ ⟩ := begin
    cases le_total a b,
    case or.inl : a_le_b {
      cases lt_or_eq_of_le a_le_b,
      case or.inl : lt { from or.inl (or.inl lt) },
      case or.inr : eq {
        subst eq,
        refine or.imp (λ le, or.inr ⟨ rfl , le ⟩) (λ le, or.inr ⟨ rfl , le ⟩) (le_total f g),
      }
    },
    case or.inr : b_le_a {
      cases lt_or_eq_of_le b_le_a,
      case or.inl : lt { from or.inr (or.inl lt) },
      case or.inr : eq {
        subst eq,
        refine or.imp (λ le, or.inr ⟨ rfl , le ⟩) (λ le, or.inr ⟨ rfl , le ⟩) (le_total f g),
      }
    }
  end

  protected noncomputable def affinity.decidable_le :
    ∀ M N, decidable (affinity.le M N)
  | ⟨ a, f, sf ⟩ ⟨ b, g, sg ⟩ :=
    if h : a = b then begin
      subst h,
      cases (decidable_linear_order.decidable_le _ f g),
      case is_true : h { from is_true (or.inr ⟨ rfl, h ⟩) },
      case is_false : h {
        have : ¬ a < a := lt_irrefl a,
        from is_false (λ x, by { rcases x with _ | ⟨ _, _ ⟩; contradiction })
      }
    end else if h' : a < b then
      is_true (or.inl h')
    else
      is_false (λ x, by { rcases x with _ | ⟨ _, _ ⟩; contradiction })

  instance affinity.linear_order : linear_order affinity :=
    { le := affinity.le,
      le_refl := affinity.le_refl,
      le_trans := affinity.le_trans,
      le_antisymm := affinity.le_antisymm,
      le_total := affinity.le_total }

  noncomputable instance : decidable_linear_order affinity :=
    { decidable_eq := affinity.decidable_eq,
      decidable_le := affinity.decidable_le,
      ..affinity.linear_order }

end ordering

end cpi

#lint
