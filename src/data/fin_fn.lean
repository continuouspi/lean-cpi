import algebra.pi_instances data.finset

set_option profiler true
set_option profiler.threshold 0.5

/-- A function which is defined everywhere, but only has "interesting" values in
    a finite set of locations.

    This is used to define a basic vector space, where every defined basis is
    known. -/
structure fin_fn (α : Type*) (β : Type*) [add_monoid β] :=
  (space : α → β)
  (defined : finset α)
  (defined_if : ∀ x, space x ≠ 0 → x ∈ defined)

namespace fin_fn
section group_instances
  variables (α : Type*) (β : Type*)

  instance [add_monoid β] : has_zero (fin_fn α β)
    := ⟨ { space := λ _, 0,
          defined := finset.empty,
          defined_if := λ x nZero, by contradiction } ⟩

  instance [add_monoid β] [decidable_eq α] : has_add (fin_fn α β) :=
    { add := λ a b,
      { space := a.space + b.space,
        defined := a.defined ∪ b.defined,
        defined_if := λ x nZero, begin
        have : a.space x + b.space x ≠ 0 := nZero,
        suffices : a.space x ≠ 0 ∨ b.space x ≠ 0,
          cases this with h h,
          case or.inl { from finset.mem_union_left _ (a.defined_if x h) },
          case or.inr { from finset.mem_union_right _ (b.defined_if x h) },

        suffices : ¬(a.space x = 0 ∧ b.space x = 0),
          from classical.not_and_distrib.mp this,

        by_contradiction h, rcases h with ⟨ a0, b0 ⟩, rw [a0, b0] at this,
        from absurd (zero_add (0 : β)) this,
        end } }

  instance [add_monoid β] [decidable_eq α] : add_monoid (fin_fn α β) :=
    { add_assoc := λ a b c, begin
        unfold_projs, simp only [],
        refine ⟨ add_assoc a.space b.space c.space, _ ⟩,

        have this := finset.union_assoc a.defined b.defined c.defined,
        unfold_projs at this, simp only [] at this,
        from this,
      end,
      zero_add := λ ⟨ space, defined, defined_if ⟩, begin
        unfold_projs, simp only [],
        from ⟨ zero_add _, finset.empty_union defined ⟩,
      end,
      add_zero := λ ⟨ space, defined, defined_if ⟩, begin
        unfold_projs, simp only [],
        from ⟨ add_zero _, finset.union_empty defined ⟩,
      end,
      ..fin_fn.has_add α β,
      ..fin_fn.has_zero α β }

  instance [add_comm_monoid β] [decidable_eq α]
    : add_comm_monoid (fin_fn α β) :=
    { add_comm := λ a b, begin
        unfold_projs, simp only [],
        refine ⟨ add_comm a.space b.space, _ ⟩,

        have this := finset.union_comm a.defined b.defined,
        unfold_projs at this, simp only [] at this,
        from this,
      end,
      ..fin_fn.add_monoid α β }

  -- Technically not a group, as (a + -a) is 0, but has a "defined" set.
  instance [add_group β] [decidable_eq α]
    : has_neg (fin_fn α β) :=
    { neg := λ a,
      { space := -a.space,
        defined := a.defined,
        defined_if := λ x nZero, a.defined_if x (neg_ne_zero.mp nZero) } }

  instance [add_group β] [decidable_eq α] : has_sub (fin_fn α β)
    := { sub := λ a b, a + -b }

  instance [semiring β] [decidable_eq α]
    : has_scalar β (fin_fn α β)
    := { smul := λ x a,
         { space := λ y, a.space y * x,
           defined := a.defined,
           defined_if := λ y nZero,
            a.defined_if y (ne_zero_of_mul_ne_zero_right nZero) } }
end group_instances

variables {α : Type*} {β : Type*}

/-- Map every basis in the fin_fn to another fin_fn, accumulating them together. -/
def bind {γ : Type} [decidable_eq γ] [add_comm_monoid β] : fin_fn α β → (α → fin_fn γ β) → fin_fn γ β
| x f := quot.lift_on x.defined.val
  (list.foldr (λ x xs, f x + xs) 0)
  (λ a b perm, begin
    induction perm,
    case list.perm.nil { from rfl },
    case list.perm.skip : x l1 l2 perm' ih { simp only [list.foldr, ih] },
    case list.perm.trans : l1 l2 l3 ab bc ihab ihbc { from (trans ihab ihbc) },
    case list.perm.swap : a b l {
      from calc  f b + (f a + list.foldr _ 0 l)
              = (f b + f a) + list.foldr _ 0 l : symm (add_assoc (f b) (f a) _)
          ... = (f a + f b) + list.foldr _ 0 l : by rw (add_comm (f b) (f a))
          ... = f a + (f b + list.foldr _ 0 l) : add_assoc (f a) (f b) _
    }
  end)

/-- `bind`, lifted to two `fin_fn`s. -/
def bind₂ {γ η : Type} [decidable_eq η] [add_comm_monoid β]
  : fin_fn α β → fin_fn γ β → (α → γ → fin_fn η β) → fin_fn η β
| x y f := bind x (λ a, bind y (f a))

end fin_fn

#lint
