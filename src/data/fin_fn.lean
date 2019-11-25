import algebra.pi_instances data.finset

/-- A function which is defined everywhere, but only has "interesting" values in
    a finite set of locations.

    This is used to define a basic vector space, where every defined basis is
    known. -/
structure fin_fn (α : Type*) (β : Type*) [add_monoid β] :=
  (space : α → β)
  (defined : finset α)
  (defined_if : ∀ x, space x ≠ 0 → x ∈ defined)

local attribute [pp_using_anonymous_constructor] fin_fn
local attribute [pp_using_anonymous_constructor] finset

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
  instance [add_group β] : has_neg (fin_fn α β) :=
    { neg := λ a,
      { space := -a.space,
        defined := a.defined,
        defined_if := λ x nZero, a.defined_if x (neg_ne_zero.mp nZero) } }

  instance [add_group β] [decidable_eq α] : has_sub (fin_fn α β)
    := { sub := λ a b, a + -b }

  instance [semiring β]
    : has_scalar β (fin_fn α β)
    := { smul := λ x a,
         { space := λ y, a.space y * x,
           defined := a.defined,
           defined_if := λ y nZero,
            a.defined_if y (ne_zero_of_mul_ne_zero_right nZero) } }

  instance [comm_ring β]
    : mul_action β (fin_fn α β) :=
    { one_smul := λ ⟨ space, defined, defined_if ⟩, begin
        simp only [has_scalar.smul],
        have : (λ (y : α), space y * 1) = space := funext(λ y, mul_one (space y)),
        from ⟨ this, rfl ⟩
      end,
      mul_smul := λ a b ⟨ space, defined, defined_if ⟩, begin
        simp only [has_scalar.smul],
        have : ((λ (y : α), space y * (a * b)) = λ (y : α), space y * b * a)
          := funext (λ y, calc  space y * (a * b)
                              = space y * (b * a) : by rw mul_comm a b
                          ... = space y * b * a : symm (mul_assoc (space y) b a)),
        from ⟨ this, rfl ⟩
      end,
    ..fin_fn.has_scalar α β }

  instance [comm_ring β] [decidable_eq α]
    : distrib_mul_action β (fin_fn α β) :=
    { smul_add := λ r x y, begin
        unfold_projs, simp only [],
        have : ((λ z, ((x.space + y.space) z) * r) = (λ z, (x.space z) * r) + λ z, (y.space z) * r)
          := funext(λ z, right_distrib (x.space z) (y.space z) r),
        from ⟨ this, rfl ⟩,
      end,
      smul_zero := λ r, begin
        simp only [has_scalar.smul, add_monoid.zero, has_zero.zero],
        have : (λ (y : α), fin_fn.space 0 y * r) = (λ _, 0) := funext (λ _, zero_mul r),
        from ⟨ this, rfl ⟩,
      end,
      ..fin_fn.mul_action α β }

  -- Like with groups, we cannot show semi_modules, as zero_smul is not true.

end group_instances

variables {α : Type*} {β : Type*}

/-- semimodule.add_smul, but without the semimodule instance.-/
@[simp]
lemma add_smul [decidable_eq α] [sr : semiring β] (r s : β) (x : fin_fn α β)
  : (r + s) • x = r • x + s • x := begin
  unfold_projs, simp only [],
  have
    : (λ y, x.space y * (r + s)) = (λ y, x.space y * r) + (λ y, x.space y * s)
    := funext (λ y, left_distrib (x.space y) r s),
  from ⟨ this, symm (finset.union_self x.defined) ⟩,
end

/-- add_group.sub_eq_add_neg but without the group instance. -/
@[simp]
lemma sub_eq_add_neg [add_group β] [decidable_eq α] (a b : fin_fn α β) : a - b = a + -b :=
  rfl

/-- Construct a fin_fn from a single value A. This returns a unit vector in the
    basis of 'A'. -/
def mk_basis [add_monoid β] [has_one β] [eq : decidable_eq α] (A : α) : fin_fn α β :=
  { space := λ B, decidable.cases_on (eq B A) (λ _, 0) (λ _, 1),
      defined := finset.singleton A,
      defined_if := λ B nZero, begin
        cases (eq B A),
        case decidable.is_false { by contradiction },
        case decidable.is_true { from finset.mem_singleton.mpr h }
      end }

/-- 'mk_basis', with an explicit decidable_eq instance. Useful for using
    classical equality. -/
def mk_basis' [add_monoid β] [has_one β] (eq : decidable_eq α) (A : α) : fin_fn α β :=
  mk_basis A

/-- Map every basis in the fin_fn to another fin_fn, accumulating them together. -/
def bind {γ : Type} [decidable_eq γ] [semiring β] : fin_fn α β → (α → fin_fn γ β) → fin_fn γ β
| X f := finset.fold (+) 0 (λ x, X.space x • (f x)) X.defined

lemma bind_zero {γ : Type} [decidable_eq γ] [semiring β] (f : α → fin_fn γ β) :
  bind 0 f = 0 := rfl

axiom bind_distrib {γ : Type} [decidable_eq α] [decidable_eq γ] [semiring β] :
  ∀ (x y : fin_fn α β) (f : α → fin_fn γ β)
  , bind (x + y) f = bind x f + bind y f

/-- `bind`, lifted to two `fin_fn`s. -/
def bind₂ {γ η : Type} [decidable_eq η] [semiring β]
  : fin_fn α β → fin_fn γ β → (α → γ → fin_fn η β) → fin_fn η β
| x y f := bind x (λ a, bind y (f a))

/-- It doesn't matter which order we do our bind in! -/
axiom bind₂_swap {α β γ η : Type} [decidable_eq η] [comm_ring β] :
  ∀ (x : fin_fn α β) (y : fin_fn γ β) (f : (α → γ → fin_fn η β))
  , bind₂ x y f = bind₂ y x (λ x y, f y x)

lemma bind₂_zero {γ η : Type} [decidable_eq η] [semiring β] (f : α → γ → fin_fn η β) :
  bind₂ 0 0 f = 0 := rfl

lemma bind₂_zero_right {γ η : Type} [decidable_eq η] [semiring β]
  (x : fin_fn γ β) (f : α → γ → fin_fn η β) :
  bind₂ 0 x f = 0 := rfl

lemma bind₂_zero_left {α β γ η : Type} [decidable_eq η] [comm_ring β]
  (x : fin_fn α β) (f : α → γ → fin_fn η β) :
  bind₂ x 0 f = 0 := by { rw (bind₂_swap x 0 f), from rfl }

end fin_fn

#lint
