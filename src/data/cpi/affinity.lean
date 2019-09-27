import data.non_neg
import data.fin.pi_order
import data.option.order

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi

/-- An affinity network.

    This is composed of $arity$ names, and a partial function $f$ which defines
    the affinities between elements of this matrix.
-/
@[derive decidable_eq]
structure affinity := intro ::
  (arity : ℕ)
  (f : fin arity → fin arity → option ℝ≥0)

section ordering

inductive affinity.le : affinity → affinity → Prop
| on_fun
    (arity : ℕ) {f g : fin arity → fin arity → option ℝ≥0}
  : f ≤ g → affinity.le ⟨ arity, f ⟩ ⟨ arity, g ⟩
| on_arity
    {arity arity' : ℕ}
    {f : fin arity → fin arity → option ℝ≥0}
    {g : fin arity' → fin arity' → option ℝ≥0}
  : arity < arity' → affinity.le ⟨ arity, f ⟩ ⟨ arity', g ⟩

open affinity.le

protected theorem affinity.le_refl : ∀ M, affinity.le M M
| ⟨ a, f ⟩ := on_fun a (le_refl f)

protected theorem affinity.le_trans :
  ∀ M N O, affinity.le M N → affinity.le N O → affinity.le M O
| ⟨ _, fm ⟩ ⟨ _, fn ⟩ ⟨ _, fo ⟩ (on_fun a le) (on_fun _ le')
  := (on_fun a (le_trans le le'))
| ⟨ _, fm ⟩ ⟨ _, fn ⟩ ⟨ ao, fo ⟩ (on_fun am le) (on_arity lt) := on_arity lt
| ⟨ am, fm ⟩ ⟨ _, fn ⟩ ⟨ _, fo ⟩ (on_arity lt) (on_fun ao le) := on_arity lt
| ⟨ am, fm ⟩ ⟨ an, fn ⟩ ⟨ ao, fo ⟩ (on_arity lt) (on_arity lt') := on_arity (lt_trans lt lt')

protected theorem affinity.le_antisymm :
  ∀ M N, affinity.le M N → affinity.le N M → M = N
| ⟨ _, f ⟩ ⟨ _, g ⟩ (on_fun a le) (on_fun b le') := by { simp, from le_antisymm le le' }
| ⟨ _, f ⟩ ⟨ _, g ⟩ (on_fun a _) (on_arity lt) := false.elim (lt_irrefl _ lt)
| ⟨ _, f ⟩ ⟨ _, g ⟩ (on_arity lt) (on_fun b _) := false.elim (lt_irrefl _ lt)
| ⟨ _, f ⟩ ⟨ _, g ⟩ (on_arity lt) (on_arity lt') := false.elim (lt_asymm lt lt')

protected theorem affinity.le_total :
  ∀ M N, affinity.le M N ∨ affinity.le N M
| ⟨ a, f ⟩ ⟨ b, g ⟩ := begin
  cases le_total a b,
  case or.inl : a_le_b {
    cases lt_or_eq_of_le a_le_b,
    case or.inl : lt { from or.inl (on_arity lt) },
    case or.inr : eq {
      subst eq,
      from or.imp (on_fun a) (on_fun a) (le_total f g)
    }
   },
  case or.inr : b_le_a {
    cases lt_or_eq_of_le b_le_a,
    case or.inl : lt { from or.inr (on_arity lt) },
    case or.inr : eq {
      subst eq,
      from or.imp (on_fun b) (on_fun b) (le_total f g)
    }
  }
end

protected noncomputable def affinity.decidable_le :
  ∀ M N, decidable (affinity.le M N)
| ⟨ a, f ⟩ ⟨ b, g ⟩ :=
  if h : a = b then begin
    subst h,
    cases (decidable_linear_order.decidable_le _ f g),
    case is_true : h { from is_true (on_fun a h) },
    case is_false : h {
        have : ¬ a < a := lt_irrefl a,
        from is_false (λ x, by { cases x; contradiction })
    }
  end else if h' : a < b then
    is_true (on_arity h')
  else
    is_false (λ x, by { cases x; contradiction })

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

#sanity_check
