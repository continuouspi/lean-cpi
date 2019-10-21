/- Ordering for functions which have a finite number of possible arguments. -/

import data.fin
import data.fintype

run_cmd lint
set_option profiler true
set_option profiler.threshold 0.5

namespace fin
namespace pi
variables {n : ℕ} {β : fin n → Type*}

private def le_worker [∀ a, has_le (β a)] [∀ a, has_lt (β a)] (f g : Π a, β a) : ∀ a, a < n → Prop
| nat.zero p := f ⟨ nat.zero, p ⟩ ≤ g ⟨ nat.zero, p ⟩
| (nat.succ a) p :=
  let f' := f ⟨ nat.succ a, p ⟩ in
  let g' := g ⟨ nat.succ a, p ⟩ in
  f' < g' ∨ (f' = g' ∧ le_worker a (nat.lt_of_succ_lt p) )

protected def le [∀ a, has_le (β a)] [∀ a, has_lt (β a)] (f g : Π a, β a) : Prop :=
  match n, rfl : ∀ (n' : ℕ), n = n' → _ with
  | nat.zero, _ := true
  | nat.succ a, r := le_worker f g a (symm r ▸ nat.lt_succ_self a)
  end

instance [∀ a, has_le (β a)] [∀ a, has_lt (β a)] : has_le (Π (a : fin n), β a)
  := ⟨ pi.le ⟩

private theorem le_refl_worker [∀ a, preorder (β a)] (f : Π a, β a)
  : ∀ a p, le_worker f f a p := λ n p, begin
  induction n; simp [le_worker],
  case nat.succ : a ih { from or.inr (ih _) }
end

protected theorem le_refl [∀ a, preorder (β a)] (f : Π a, β a) : pi.le f f := begin
  tactic.unfreeze_local_instances,
  cases n,

  case nat.zero { unfold pi.le },
  case nat.succ : a { unfold pi.le, from le_refl_worker f _ _ }
end

private theorem le_trans_worker [∀ a, preorder (β a)] (f g h : Π a, β a)
  : ∀ a p, le_worker f g a p → le_worker g h a p → le_worker f h a p
| nat.zero _ fg gf := le_trans fg gf
| (nat.succ x) p fg gh :=
  match fg, gh with
  | or.inl fg, or.inl gh := or.inl (lt_trans fg gh)
  | or.inl fg, or.inr ⟨ gh, _ ⟩ := or.inl (gh ▸ fg)
  | or.inr ⟨ fg, _ ⟩, or.inl gh := or.inl (symm fg ▸ gh)
  | or.inr ⟨ fg', ihl ⟩, or.inr ⟨ gh', ihr ⟩ := or.inr $
    by { simp [fg', gh'], from le_trans_worker _ _ ihl ihr }
  end

protected theorem le_trans [∀ a, preorder (β a)] (f g h : Π a, β a)
  : pi.le f g → pi.le g h → pi.le f h := λ fg gh, begin
  tactic.unfreeze_local_instances,
  cases n,

  case nat.zero { unfold pi.le },
  case nat.succ : a {
    unfold pi.le at fg gh ⊢,
    from le_trans_worker f g h _ _ fg gh
  }
end

instance [∀ a, preorder (β a)] : preorder (Π (a : fin n), β a)
  := { le := pi.le, le_refl := pi.le_refl, le_trans := pi.le_trans }

private theorem le_antisymm_worker [∀ a, partial_order (β a)] (f g : Π a, β a)
  : Π a p, le_worker f g a p → le_worker g f a p
  → ∀ x (H : x ≤ a), f ⟨ x, nat.lt_of_le_of_lt H p ⟩ = g ⟨ x, nat.lt_of_le_of_lt H p ⟩
| nat.zero p fg gf ._ (nat.less_than_or_equal.refl 0) := le_antisymm fg gf
| (nat.succ a) p (or.inl lt) (or.inl lt') _ _ := false.elim (lt_asymm lt lt')
| (nat.succ a) p (or.inl lt) (or.inr ⟨ eq, _ ⟩) _ _ := false.elim (ne_of_lt lt (symm eq))
| (nat.succ a) p (or.inr ⟨ eq, _ ⟩) (or.inl lt) _ _ := false.elim (ne_of_lt lt (symm eq))
| (nat.succ a) p (or.inr ⟨ eq, ihl ⟩) (or.inr ⟨ _, ihr ⟩) x (nat.less_than_or_equal.refl n) := eq
| (nat.succ a) p (or.inr ⟨ eq, ihl ⟩) (or.inr ⟨ _, ihr ⟩) x (nat.less_than_or_equal.step le)
  := le_antisymm_worker a _ ihl ihr x le

protected theorem le_antisymm [∀ a, partial_order (β a)] (f g : Π a, β a)
  : f ≤ g → g ≤ f → f = g := λ fg gf, begin
    tactic.unfreeze_local_instances,
    cases n,

    case nat.zero { from funext (λ ⟨ _, lt ⟩, match lt with end) },
    case nat.succ : a {
      from funext
        (λ ⟨ x, lt ⟩, le_antisymm_worker f g a _ fg gf x (nat.le_of_lt_succ lt))
    }
  end

instance [∀ a, partial_order (β a)] : partial_order (Π (a : fin n), β a)
  := { le_antisymm := pi.le_antisymm, ..pi.preorder }

private def le_decidable_worker
  [∀ a, has_le (β a)] [∀ a, has_lt (β a)] [∀ a, decidable_eq (β a)]
  [∀ a, @decidable_rel (β a) (<)] [∀ a, @decidable_rel (β a) (≤)]
  (f g : Π a, β a) : Π (a : ℕ) (p : a < n), decidable (le_worker f g a p)
| nat.zero _ := by { unfold le_worker, by apply_instance }
| (nat.succ a) p := @or.decidable _ _ _ (@and.decidable _ _ _ (le_decidable_worker a _))

protected def le_decidable
  [∀ a, has_le (β a)] [∀ a, has_lt (β a)] [∀ a, decidable_eq (β a)]
  [∀ a, @decidable_rel (β a) (<)] [∀ a, @decidable_rel (β a) (≤)]
  (f g : Π a, β a) : decidable (f ≤ g) := begin
    tactic.unfreeze_local_instances,
    cases n,

    case nat.zero { from decidable.true },
    case nat.succ : a { from le_decidable_worker f g a _ }
end

instance decidable_le
  [∀ a, has_le (β a)] [∀ a, has_lt (β a)] [∀ a, decidable_eq (β a)]
  [∀ a, @decidable_rel (β a) (<)] [∀ a, @decidable_rel (β a) (≤)]
  : @decidable_rel (Π (a : fin n), β a) (≤)
  := pi.le_decidable

private theorem le_total_worker [∀ a, linear_order (β a)] (f g : Π a, β a)
  : ∀ a p, le_worker f g a p ∨ le_worker g f a p
| nat.zero p := le_total (f ⟨ 0, p ⟩) (g ⟨ 0, p ⟩)
| (nat.succ a) p := by {
  cases (le_total (f ⟨ _, p ⟩) (g ⟨ _, p ⟩)),
  case or.inl : f_le_g {
    cases lt_or_eq_of_le f_le_g,
    -- f _ < g _ : Trivial: build inl
    case or.inl : f_lt_g { from or.inl (or.inl f_lt_g) },
    -- f _ = g _ : Recurse: build inr
    case or.inr : f_eq_g {
      from or.imp (λ h, or.inr ⟨ f_eq_g, h ⟩) (λ h, or.inr ⟨ symm f_eq_g, h ⟩)
                  (le_total_worker a _)
    }
  },
  case or.inr : g_le_f {
    -- As above, but flipped.
    cases lt_or_eq_of_le g_le_f,
    case or.inl : g_lt_f { from or.inr (or.inl g_lt_f) },
    case or.inr : g_eq_f {
      from or.imp (λ h, or.inr ⟨ symm g_eq_f, h ⟩) (λ h, or.inr ⟨ g_eq_f, h ⟩)
                  (le_total_worker a _)
    }
  }
 }

protected theorem le_total [∀ a, linear_order (β a)] (f g : Π a, β a) : f ≤ g ∨ g ≤ f := begin
  tactic.unfreeze_local_instances,
  cases n,

  case nat.zero { from or.inl true.intro },
  case nat.succ : a { from le_total_worker f g a _ }
end

instance [∀ a, linear_order (β a)] : linear_order (Π (a : fin n), β a)
  := { le_total := pi.le_total, ..pi.partial_order }

instance [∀ a, decidable_linear_order (β a)] : decidable_linear_order (Π (a : fin n), β a)
  := { decidable_le := pi.decidable_le,
       decidable_eq := fintype.decidable_pi_fintype,
       ..pi.linear_order }

end pi
end fin

#lint
