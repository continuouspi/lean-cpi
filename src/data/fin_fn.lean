import algebra.pi_instances data.finset

/-- A function which is defined everywhere, but only has "interesting" values in
    a finite set of locations.

    This is used to define a basic vector space, where every defined basis is
    known. -/
@[nolint has_inhabited_instance]
structure fin_fn (α : Type*) (β : Type*) [has_zero β] :=
  (space : α → β)
  (support : finset α)
  (support_iff : ∀ x, space x ≠ 0 ↔ x ∈ support)

local attribute [pp_using_anonymous_constructor] fin_fn
local attribute [pp_using_anonymous_constructor] finset

namespace fin_fn

section helpers
  variables {α : Type*} {β₁ : Type*} {β₂ : Type*} {β : Type*} [has_zero β₁] [has_zero β₂] [has_zero β]

  /-- Map over a finite set, assuming the support set doesn't grow. -/
  def on_finset [decidable_eq β] (s : finset α) (f : α → β) (hf : ∀a, f a ≠ 0 → a ∈ s) : fin_fn α β :=
    ⟨ f,
      s.filter (λa, f a ≠ 0),
      λ x, ⟨ λ h, finset.mem_filter.mpr ⟨ hf x h, h ⟩, λ h, (finset.mem_filter.mp h).2 ⟩ ⟩

  /-- Zip over two support sets, assuming the operation preserves 0. -/
  def zip_with [decidable_eq α] [decidable_eq β₁] [decidable_eq β]
    (f : β₁ → β₂ → β) (zero : f 0 0 = 0) (g₁ : fin_fn α β₁) (g₂ : fin_fn α β₂) : (fin_fn α β) :=
    on_finset (g₁.support ∪ g₂.support) (λa, f (g₁.space a) (g₂.space a)) (λ a not_zero, begin
      rw [finset.mem_union, (g₁.support_iff _).symm, (g₂.support_iff _).symm, ne, ← not_and_distrib],
      rintro ⟨ h₁, h₂ ⟩, rw [h₁, h₂] at not_zero, from not_zero zero,
    end)

  /-- Function extensionality lifted to fin_fns. -/
  @[ext]
  lemma ext : ∀ {f g : fin_fn α β}, (∀ a, f.space a = g.space a) → f = g
  | ⟨ f, sf, iff_f ⟩ ⟨ g, sg, iff_g ⟩ lift := begin
    have : f = g := funext lift, subst this,
    have : sf = sg := finset.ext' (λ a, (iff_f a).symm.trans (iff_g a)), subst this,
  end

  /-- Apply a 0-preserving function over the range of our fin_fn. -/
  def map_range [decidable_eq β] (f : β₁ → β) (zero : f 0 = 0) (g : fin_fn α β₁) : fin_fn α β :=
    on_finset g.support (f ∘ g.space) (λ a not_zero, begin
      rw [(g.support_iff _).symm],
      assume is_zero, rw [function.comp_app, is_zero] at not_zero, from not_zero zero,
    end)

  lemma unsupported_zero [decidable_eq β] {x : α} {f : fin_fn α β} : x ∉ f.support ↔ f.space x = 0
    := ⟨ λ nmem, by_contradiction (λ h, nmem ((f.support_iff x).mp h)),
         λ zero mem, (f.support_iff x).mpr mem zero ⟩
end helpers

section group_instances
  variables (α : Type*) (β : Type*)

  instance [has_zero β] : has_zero (fin_fn α β)
    := ⟨ { space := λ _, 0,
          support := finset.empty,
          support_iff := λ x, ⟨ λ nZero, by contradiction, λ x, by cases x ⟩ } ⟩

  instance [add_monoid β] [decidable_eq α] [decidable_eq β] : has_add (fin_fn α β) :=
    { add := zip_with(+) (add_zero 0) }

  instance [add_monoid β] [decidable_eq α] [decidable_eq β] : add_monoid (fin_fn α β) :=
    { add_assoc := λ a b c, ext (λ x, add_assoc _ _ _),
      zero_add := λ a, ext (λ x, zero_add _),
      add_zero := λ a, ext (λ x, add_zero _),
      ..fin_fn.has_add α β,
      ..fin_fn.has_zero α β }

  instance [add_comm_monoid β] [decidable_eq α] [decidable_eq β]
    : add_comm_monoid (fin_fn α β) :=
    { add_comm := λ a b, ext (λ x, add_comm _ _),
      ..fin_fn.add_monoid α β }

  instance [add_group β] [decidable_eq β] : has_neg (fin_fn α β) :=
    { neg := map_range has_neg.neg neg_zero }

  instance [add_comm_group β] [decidable_eq α] [decidable_eq β] : add_comm_group (fin_fn α β) :=
    { add_left_neg := λ f, ext (λ a, add_left_neg _),
      ..fin_fn.add_comm_monoid α β,
      ..fin_fn.has_neg α β  }

  instance [semiring β] [decidable_eq β]
    : has_scalar β (fin_fn α β)
    := { smul := λ a, map_range ((•) a) (smul_zero _) }

  instance [comm_ring β] [decidable_eq β]
    : mul_action β (fin_fn α β) :=
    { one_smul := λ f, ext (λ a, one_smul _ _),
      mul_smul := λ x y f, ext (λ a, mul_smul _ _ _),
    ..fin_fn.has_scalar α β }

  instance [comm_ring β] [decidable_eq α] [decidable_eq β]
    : distrib_mul_action β (fin_fn α β) :=
    { smul_add := λ r x y, ext (λ a, smul_add _ _ _),
      smul_zero := λ r, ext (λ a, smul_zero _),
      ..fin_fn.mul_action α β }

  instance [comm_ring β] [decidable_eq α] [decidable_eq β]
    : semimodule β (fin_fn α β) :=
    { add_smul := λ r s f, ext (λ a, right_distrib _ _ _),
      zero_smul := λ f, ext (λ a, zero_mul _),
      ..fin_fn.distrib_mul_action α β,
    }

end group_instances

variables {α : Type*} {β : Type*}

/-- Construct a fin_fn from a single value A. This returns a unit vector in the
    basis of 'A'. -/
def single [add_monoid β] [decidable_eq α] [decidable_eq β] (A : α) (b : β): fin_fn α β :=
  { space := λ B, if A = B then b else 0,
    support := if 0 = b then ∅ else finset.singleton A,
    support_iff := λ B, begin
      by_cases is_zero : 0 = b; by_cases is_eq : A = B; simp only [is_zero, is_eq, if_pos, if_false],
      { from ⟨ λ x, by contradiction, false.elim ⟩ },
      { from ⟨ λ x, by contradiction, false.elim ⟩ },
      { from ⟨ λ _, finset.mem_singleton.mpr rfl, λ _, ne.symm is_zero ⟩ },
      { from ⟨ λ x, by contradiction, λ mem, absurd (finset.mem_singleton.mp mem).symm is_eq ⟩ },
    end }

/-- Map every basis in the fin_fn to another fin_fn, accumulating them together. -/
def bind {γ : Type} [decidable_eq γ] [decidable_eq β] [semiring β] : fin_fn α β → (α → fin_fn γ β) → fin_fn γ β
| X f := finset.sum X.support (λ x, X.space x • (f x))

lemma bind_zero {γ : Type} [decidable_eq γ] [decidable_eq β] [semiring β] (f : α → fin_fn γ β) :
  bind 0 f = 0 := rfl

lemma empty_zero [has_zero β] [decidable_eq β] : ∀ (f : fin_fn α β), f.support = ∅ → f = 0
| ⟨ f, _, iff ⟩ ⟨ _ ⟩ := ext (λ x, by_contradiction (iff x).mp)

lemma bind_distrib {γ : Type} [comm_ring β] [decidable_eq α] [decidable_eq γ] [decidable_eq β] :
  ∀ (x y : fin_fn α β) (f : α → fin_fn γ β)
  , bind (x + y) f = bind x f + bind y f
-- | ⟨ fx, xs, xif ⟩ ⟨ fy, ys, yif ⟩ f := begin
--   -- have : ∀ a, (x + y).space a = x.space a + y.space a := λ x, rfl,
--   simp only [bind],
--   unfold_projs,
--   unfold zip_with on_finset,
| x y f := begin
  show finset.sum (finset.filter (λ a, x.space a + y.space a ≠ 0) (x.support ∪ y.support))
        (λ a, (x.space a + y.space a) • f a)
     = finset.sum x.support (λ a, x.space a • f a) + finset.sum y.support (λ a, y.space a • f a),

  have : finset.sum (finset.filter (λ a, x.space a + y.space a ≠ 0) (x.support ∪ y.support))
           (λ a, (x.space a + y.space a) • f a)
       = finset.sum (x.support ∪ y.support) (λ a, (x.space a + y.space a) • f a)
       := finset.sum_subset (finset.filter_subset (x.support ∪ y.support)) (λ a mem not_mem, begin
      suffices : x.space a + y.space a = 0, simp only [this, zero_smul],

      by_contradiction not_zero,
      have h := finset.mem_sdiff.mpr ⟨ mem, not_mem ⟩,
      rw ← finset.filter_not at h,
      from (finset.mem_filter.mp h).2 not_zero,
    end),
  rw this,

  rw finset.sum_subset (finset.subset_union_left x.support y.support) (λ a mem not_x, begin
    show (λ a, x.space a • f a) a = 0,
    simp only [unsupported_zero.mp not_x, zero_smul],
  end),
  rw finset.sum_subset (finset.subset_union_right x.support y.support) (λ a mem not_y, begin
    show (λ a, y.space a • f a) a = 0,
    simp only [unsupported_zero.mp not_y, zero_smul],
  end),

  simp only [add_smul, finset.sum_add_distrib],
end

/-- `bind`, lifted to two `fin_fn`s. -/
def bind₂ {γ η : Type} [decidable_eq η] [decidable_eq β] [semiring β]
  : fin_fn α β → fin_fn γ β → (α → γ → fin_fn η β) → fin_fn η β
| x y f := bind x (λ a, bind y (f a))

lemma bind₂_zero {γ η : Type} [decidable_eq η] [decidable_eq β] [semiring β]  (f : α → γ → fin_fn η β) :
  bind₂ 0 0 f = 0 := rfl

lemma bind₂_zero_right {γ η : Type} [decidable_eq η] [decidable_eq β] [semiring β]
  (x : fin_fn γ β) (f : α → γ → fin_fn η β) :
  bind₂ 0 x f = 0 := rfl

/-- It doesn't matter which order we do our bind in! -/
lemma bind₂_swap {α β γ η : Type*} [decidable_eq η] [decidable_eq β] [comm_ring β] :
  ∀ (x : fin_fn α β) (y : fin_fn γ β) (f : (α → γ → fin_fn η β))
  , bind₂ x y f = bind₂ y x (λ x y, f y x)
| x y f := begin
  show finset.sum x.support (λ a, x.space a • finset.sum y.support (λ b, y.space b • f a b))
     = finset.sum y.support (λ a, y.space a • finset.sum x.support (λ b, x.space b • f b a)),

  have : ∀ a b, y.space a • x.space b • f b a = x.space b • y.space a • f b a
    := λ a b, smul_comm (y.space a) _ _,
  simp only [finset.smul_sum, this],

  simp only [finset.sum_eq_multiset_sum],
  from multiset.sum_map_sum_map x.support.val y.support.val,
end

lemma bind₂_zero_left {α β γ η : Type} [decidable_eq β] [decidable_eq η] [comm_ring β]
  (x : fin_fn α β) (f : α → γ → fin_fn η β) :
  bind₂ x 0 f = 0 := by { rw (bind₂_swap x 0 f), from rfl }

end fin_fn

#lint-
