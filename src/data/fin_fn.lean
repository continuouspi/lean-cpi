import algebra.pi_instances algebra.half_ring data.finset

/-- A function which is defined everywhere, but only has "interesting" values in
    a finite set of locations.

    This is used to define a basic vector space, where every defined basis is
    known. -/
structure fin_fn (α : Type*) (β : Type*) [has_zero β] :=
  (space : α → β)
  (support : finset α)
  (support_iff : ∀ x, space x ≠ 0 ↔ x ∈ support)

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

  /-- Function extensionality lifted to fin_fns. -/
  lemma ext' [decidable_eq β] : ∀ {f g : fin_fn α β}, f.support = g.support → (∀ a ∈ f.support, f.space a = g.space a) → f = g
  | ⟨ f, sf, iff_f ⟩ ⟨ g, _, iff_g ⟩ eql lift := begin
    simp only [] at eql, subst eql,
    suffices : ∀ a, f a = g a, from ext this,

    assume a,
    cases classical.prop_decidable (a ∈ sf),
    case is_true { from lift a h },
    case is_false {
      have : f a = 0,
      { have : a ∉ (fin_fn.mk f sf iff_f).support := h,
        from (unsupported_zero.mp this) },
      have : g a = 0,
      { have : a ∉ (fin_fn.mk g sf iff_g).support := h,
        from (unsupported_zero.mp this) },

      rw [‹f a = 0›, ‹g a = 0›],
    }
  end

  /-- Convert this fin_fn to a string, using a specific separator (such as "+"). -/
  protected def to_string [has_repr α] [has_repr β] : string → fin_fn α β → string
  | sep x := string.intercalate sep ((x.support.val.map (λ a, repr (x.space a) ++ " • " ++ repr a)).sort (≤))
end helpers

section monoid_instances
  variables (α : Type*) (β : Type*)

  instance [has_repr α] [has_repr β] [has_zero β] : has_repr (fin_fn α β) := ⟨ fin_fn.to_string "+" ⟩

  instance [has_zero β] : has_zero (fin_fn α β)
    := ⟨ { space := λ _, 0,
          support := finset.empty,
          support_iff := λ x, ⟨ λ nZero, by contradiction, λ x, by cases x ⟩ } ⟩

  instance [has_zero β] : inhabited (fin_fn α β) := ⟨ 0 ⟩

  instance [add_monoid β] [decidable_eq α] [decidable_eq β] : has_add (fin_fn α β) :=
    { add := zip_with (+) (add_zero 0) }

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

  instance [has_zero β] [decidable_eq α] [decidable_eq β] : decidable_eq (fin_fn α β)
  | ⟨ a_f, a_space, a_iff ⟩ ⟨ b_f, b_space, b_iff ⟩ :=
    if eq_space : a_space = b_space then
      if eq_f : ∀ a ∈ a_space, a_f a = b_f a then
        is_true (ext' eq_space eq_f)
      else is_false (λ x, begin
        have h := (fin_fn.mk.inj x).1, subst h,
        from eq_f (λ x mem, rfl),
      end)
    else is_false (λ x, eq_space (fin_fn.mk.inj x).2)

  instance [add_monoid β] [decidable_eq α] [decidable_eq β] (a : α) : is_add_monoid_hom (λ f : fin_fn α β, f.space a)
    := { map_add := λ a b, rfl, map_zero := rfl }

end monoid_instances

section bulk_operations
variables {α : Type*} {β : Type*}

/-- Construct a fin_fn from a single value A. This returns a unit vector in the
    basis of 'A'. -/
def single [has_zero β] [decidable_eq α] [decidable_eq β] (A : α) (b : β) : fin_fn α β :=
  { space := λ B, if A = B then b else 0,
    support := if 0 = b then ∅ else finset.singleton A,
    support_iff := λ B, begin
      by_cases is_zero : 0 = b; by_cases is_eq : A = B; simp only [is_zero, is_eq, if_pos, if_false],
      { from ⟨ λ x, by contradiction, false.elim ⟩ },
      { from ⟨ λ x, by contradiction, false.elim ⟩ },
      { from ⟨ λ _, finset.mem_singleton.mpr rfl, λ _, ne.symm is_zero ⟩ },
      { from ⟨ λ x, by contradiction, λ mem, absurd (finset.mem_singleton.mp mem).symm is_eq ⟩ },
    end }

lemma single.inj [has_zero β] [decidable_eq α] [decidable_eq β] (A : α)
  : function.injective (@single α β _ _ _ A)
| b₁ b₂ eql := begin
  have : (single A b₁).space A = (single A b₂).space A, rw eql,
  simpa only [single, if_pos] using this,
end

@[simp]
lemma single_zero [has_zero β] [decidable_eq α] [decidable_eq β] (a : α) : single a (0 : β) = 0
  := by { simp only [single, if_pos, if_t_t], from rfl }

@[simp]
lemma single_add [add_monoid β] [decidable_eq α] [decidable_eq β] (a : α) (b₁ b₂ : β) :
  single a (b₁ + b₂) = single a b₁ + single a b₂
  := ext (λ x, begin
    show ite (a = x) (b₁ + b₂) 0 = ite (a = x) b₁ 0 + ite (a = x) b₂ 0,
    by_cases a = x; simp only [h, if_pos, if_false, add_zero],
  end)

/-- `sum f g` is the sum of `g a (f a)` over the support of `f`. -/
def sum {γ : Type*} [has_zero β] [add_comm_monoid γ] (f : fin_fn α β) (g : α → β → γ) : γ
  := f.support.sum (λa, g a (f.space a))

@[simp]
lemma sum_single_index {γ : Type*} [add_comm_monoid γ] [comm_ring β] [decidable_eq α] [decidable_eq β]
  (a : α) (b : β) (f : α → β → γ) (zero : ∀ x, f x 0 = 0): (single a b).sum f = f a b := begin
  by_cases 0 = b; simp only [sum, single, if_pos, if_false, h],
  { simp only [finset.sum_empty, h.symm, zero] },
  { simp only [finset.sum_singleton, if_pos] },
end

lemma sum_distrib {γ : Type*} [decidable_eq α] [decidable_eq β] [add_comm_monoid β] [add_comm_monoid γ] {x y : fin_fn α β}
  {h : α → β → γ} (h_zero : ∀ a, h a 0 = 0) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) :
  (x + y).sum h = x.sum h + y.sum h := begin
  show finset.sum (finset.filter (λ a, x.space a + y.space a ≠ 0) (x.support ∪ y.support))
          (λ a, h a (x.space a + y.space a))
     = x.sum h + y.sum h,

  have : finset.sum (finset.filter (λ a, x.space a + y.space a ≠ 0) (x.support ∪ y.support))
           (λ a, h a (x.space a + y.space a))
       = finset.sum (x.support ∪ y.support) (λ a, h a (x.space a + y.space a))
       := finset.sum_subset (finset.filter_subset (x.support ∪ y.support)) (λ a mem not_mem, begin
      suffices : x.space a + y.space a = 0, simp only [h_zero, this],

      by_contradiction not_zero,
      have h := finset.mem_sdiff.mpr ⟨ mem, not_mem ⟩,
      rw ← finset.filter_not at h,
      from (finset.mem_filter.mp h).2 not_zero,
    end),
  rw this,

  have hx : x.sum h = finset.sum (x.support ∪ y.support) (λ a, h a (x.space a))
    := finset.sum_subset (finset.subset_union_left x.support y.support)
        (λ a mem not_x, by simp only [unsupported_zero.mp not_x, h_zero]),
  have hy : y.sum h = finset.sum (x.support ∪ y.support) (λ a, h a (y.space a))
    := finset.sum_subset (finset.subset_union_right x.support y.support)
        (λ a mem not_y, by simp only [unsupported_zero.mp not_y, h_zero]),

  simp only [hx, hy, h_add, finset.sum_add_distrib],
end

@[simp]
lemma sum_zero {γ : Type*} [has_zero β] [add_comm_monoid γ] (f : α → β → γ) : sum 0 f = 0 := rfl

@[simp]
lemma sum_const_zero {γ : Type*} [has_zero β] [add_comm_monoid γ] (f : fin_fn α β): sum f (λ _ _, (0 : γ)) = 0
  := finset.sum_const_zero

/-- Map every basis in the fin_fn to another fin_fn, accumulating them together. -/
def bind {γ : Type*} [decidable_eq γ] [decidable_eq β] [semiring β] (f : fin_fn α β) (g : α → fin_fn γ β) : fin_fn γ β
  := sum f (λ x c, c • g x)

@[simp]
lemma bind_zero {γ : Type} [decidable_eq γ] [decidable_eq β] [semiring β] (f : α → fin_fn γ β) : bind 0 f = 0 := sum_zero _

lemma empty_zero [has_zero β] [decidable_eq β] : ∀ (f : fin_fn α β), f.support = ∅ → f = 0
| ⟨ f, _, iff ⟩ ⟨ _ ⟩ := ext (λ x, by_contradiction (iff x).mp)

@[simp]
lemma sum_sum_index {γ : Type*} {α₁: Type*} {β₁ : Type*} [decidable_eq α] [decidable_eq α₁] [decidable_eq β]
  [add_comm_monoid β₁] [add_comm_monoid β] [add_comm_monoid γ]
  {f : fin_fn α₁ β₁} {g : α₁ → β₁ → fin_fn α β}
  {h : α → β → γ} (h_zero : ∀a, h a 0 = 0) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) :
  (f.sum g).sum h = f.sum (λa b, (g a b).sum h) := begin
    show (finset.sum f.support (λ (a : α₁), g a (f.space a))).sum h
       = finset.sum f.support _,
    induction f.support using finset.induction_on with a s not_mem ih,
    from rfl,
    { rw [finset.sum_insert not_mem, finset.sum_insert not_mem, ← ih, sum_distrib h_zero h_add], },
  end

lemma bind_distrib {γ : Type} [comm_ring β] [decidable_eq α] [decidable_eq γ] [decidable_eq β] :
  ∀ (x y : fin_fn α β) (f : α → fin_fn γ β)
  , bind (x + y) f = bind x f + bind y f
| x y f := begin
  have zero : ∀ a, (λ (x : α) (c : β), c • f x) a 0 = 0 := λ _, by simp only [zero_smul],
  have add : ∀ (a : α) (b₁ b₂ : β)
           , (λ (x : α) (c : β), c • f x) a (b₁ + b₂)
           = (λ (x : α) (c : β), c • f x) a b₁ + (λ (x : α) (c : β), c • f x) a b₂
           := λ _ _ _, by simp only [add_smul],
  simp only [sum_distrib zero add, bind],
end

lemma bind_smul {γ : Type} [comm_ring β] [decidable_eq α] [decidable_eq γ] [decidable_eq β] :
  ∀ (c : β) (x : fin_fn α β) (f : α → fin_fn γ β)
  , c • bind x f = bind (c • x) f
| c x f := begin
  simp only [bind, sum],

  have : (c • x).support ⊆ x.support := finset.filter_subset _,
  rw finset.sum_subset this (λ a mem not_mem, begin
    show (λ a, (c • x).space a • f a) a = 0,
    simp only [],
    rw [unsupported_zero.mp not_mem, zero_smul],
  end), simp only [], clear this,

  -- Then follow the same proof as prod_pow.
  induction x.support using finset.induction_on with a f not_mem ih,
  { simp only [finset.sum_empty, smul_zero] },
  {
    simp only [finset.sum_insert not_mem],
    rw [smul_add, ← mul_smul, ih],
    from rfl,
  },
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

@[simp]
lemma bind_single {γ : Type} [comm_ring β] [decidable_eq α] [decidable_eq γ] [decidable_eq β] :
  ∀ (a : α) (b : β) (f : α → fin_fn γ β)
  , bind (single a b) f = b • f a
| a b f := sum_single_index a b _ (λ x, zero_smul _ _)

@[simp]
lemma sum_single [decidable_eq α] [decidable_eq β] [add_comm_monoid β] (f : fin_fn α β)
  : f.sum single = f := begin
  suffices : ∀ (a : α), (sum f single).space a = f.space a, from ext this,
  assume a,

  suffices : finset.sum f.support (λ (x : α), ite (x = a) (f.space x) 0) = f.space a,
  { have h := (f.support.sum_hom (λ f : fin_fn α β, f.space a)).symm,
    refine trans h _,
    simp only [single, this] },

  by_cases h : a ∈ f.support,
  { have : (finset.singleton a : finset α) ⊆ f.support,
    { simpa only [finset.subset_iff, finset.mem_singleton, forall_eq] },

    rw ← finset.sum_subset this (λ b mem not_mem, begin
      show ite (b = a) (f.space b) 0 = 0,
      simp only [if_neg (finset.not_mem_singleton.mp not_mem)],
    end),
    simp only [finset.sum_singleton, if_pos (eq.refl a)],
  },

  {
    calc  finset.sum f.support (λ (x : α), ite (x = a) (f.space x) 0)
        = f.support.sum (λ a, (0 : β)) : finset.sum_congr rfl (λ b mem, begin
            by_cases (b = a), { subst h, contradiction },
            simp only [if_neg h],
          end)
    ... = 0 : finset.sum_const_zero
    ... = f.space a : (unsupported_zero.mp h).symm
  },
end

end bulk_operations

section group_instances
  variables (α : Type*) (β : Type*)

  instance [decidable_eq α] [decidable_eq β] [has_zero α] [has_zero β] [has_one β] : has_one (fin_fn α β) :=
    { one := single 0 1 }

  instance [decidable_eq α] [decidable_eq β] [has_add α] [semiring β] : has_mul (fin_fn α β) :=
    { mul := λ f g, f.sum $ λ a₁ b₁, g.sum $ λ a₂ b₂, single (a₁ + a₂) (b₁ * b₂) }

  instance [decidable_eq α] [decidable_eq β] [add_semigroup α] [comm_ring β] : semigroup (fin_fn α β)
    := { mul_assoc := λ a b c, begin
      show sum
        (sum a (λ (a₁ : α) (b₁ : β), sum b (λ (a₂ : α) (b₂ : β), single (a₁ + a₂) (b₁ * b₂))))
          (λ (a₁ : α) (b₁ : β), sum c (λ (a₂ : α) (b₂ : β), single (a₁ + a₂) (b₁ * b₂)))
      = sum a (λ (a₁ : α) (b₁ : β)
              , sum (sum b (λ (a₁ : α) (b₁ : β), sum c (λ (a₂ : α) (b₂ : β), single (a₁ + a₂) (b₁ * b₂))))
                    (λ (a₂ : α) (b₂ : β), single (a₁ + a₂) (b₁ * b₂))),

      have zero : ∀ (a' : α) (b' : β) a, (λ a b, single (a' + a) (b' * b)) a 0 = 0
        := λ _ _ a, by simp only [mul_zero, single_zero, sum_const_zero],

      have add : ∀ (a' : α) (b' : β) (a : α) (b₁ b₂ : β)
               , single (a' + a) (b' * (b₁ + b₂))
               = single (a' + a) (b' * b₁) + single (a' + a) (b' * b₂)
        := λ _ _ a b₁ b₂, by simp only [left_distrib, single_add],

      have this :
        ∀ (a : fin_fn α β) (f : α → β → fin_fn α β)
        , sum (sum a f) (λ a₁ b₁, sum c (λ a₂ b₂, single (a₁ + a₂) (b₁ * b₂)))
        = sum a (λ a b, sum (f a b) (λ a₁ b₁, sum c (λ a₂ b₂, single (a₁ + a₂) (b₁ * b₂))))
        := λ a f, sum_sum_index
            (λ a, by { simp only [zero_mul, single_zero, sum_const_zero] })
            (λ a b₁ b₂, by simp only [sum, right_distrib, single_add, finset.sum_add_distrib]),
      simp only [this], clear this,
      simp [sum_single_index, sum_sum_index (zero _ _) (add _ _), mul_assoc],
    end,
    ..fin_fn.has_mul α β }

  instance [decidable_eq α] [decidable_eq β] [add_monoid α] [comm_ring β] : monoid (fin_fn α β) :=
    { one_mul := λ a, begin
        show sum (single 0 1) (λ a₁ b₁, sum a (λ a₂ b₂, single (a₁ + a₂) (b₁ * b₂))) = a,
        simp,
      end,
      mul_one := λ a, begin
        show sum a (λ a₁ b₁, sum (single (0 : α) (1 : β)) (λ a₂ b₂, single (a₁ + a₂) (b₁ * b₂))) = a,
        simp,
      end,
      ..fin_fn.has_one α β,
      ..fin_fn.semigroup α β }

  instance [decidable_eq α] [decidable_eq β] [add_comm_monoid α] [comm_ring β] : comm_monoid (fin_fn α β) :=
    { mul_comm := λ a b, begin
        show sum a (λ a₁ b₁, sum b (λ a₂ b₂, single (a₁ + a₂) (b₁ * b₂)))
           = sum b (λ a₁ b₁, sum a (λ a₂ b₂, single (a₁ + a₂) (b₁ * b₂))),

        suffices : sum a (λ a₁ b₁, sum b (λ a₂ b₂, single (a₁ + a₂) (b₁ * b₂)))
                 = sum b (λ a₁ b₁, sum a (λ a₂ b₂, single (a₂ + a₁) (b₂ * b₁))),
        { simpa only [add_comm, mul_comm] using this },

        simp only [sum, finset.sum_eq_multiset_sum],
        from multiset.sum_map_sum_map a.support.val b.support.val,
      end
      ..fin_fn.monoid α β }

  instance [decidable_eq α] [decidable_eq β] [has_add α] [semiring β] : mul_zero_class (fin_fn α β) :=
    { zero_mul := λ x, by simp only [has_mul.mul, sum_zero],
      mul_zero := λ x, by simp only [has_mul.mul, sum_zero, sum_const_zero],
      ..fin_fn.has_zero α β,
      ..fin_fn.has_mul α β }

  instance [decidable_eq α] [decidable_eq β] [has_add α] [semiring β] : distrib (fin_fn α β) :=
    { left_distrib := λ a b c, begin
        show sum a (λ a₁ b₁, sum (b + c) (λ a₂ b₂, single (a₁ + a₂) (b₁ * b₂)))
           = sum a (λ a₁ b₁, sum b (λ a₂ b₂, single (a₁ + a₂) (b₁ * b₂)))
           + sum a (λ a₁ b₁, sum c (λ a₂ b₂, single (a₁ + a₂) (b₁ * b₂))),

        have zero : ∀ (a' : α) (b' : β) a, (λ a b, single (a' + a) (b' * b)) a 0 = 0
          := λ _ _ a, by simp only [mul_zero, single_zero, sum_const_zero],

        have add : ∀ (a' : α) (b' : β) (a : α) (b₁ b₂ : β)
                , single (a' + a) (b' * (b₁ + b₂))
                = single (a' + a) (b' * b₁) + single (a' + a) (b' * b₂)
          := λ _ _ a b₁ b₂, by simp only [left_distrib, single_add],

        simp only [sum_distrib (zero _ _) (add _ _)],
        from finset.sum_add_distrib,
      end,
      right_distrib := λ a b c, sum_distrib
          (λ a, by { simp only [zero_mul, single_zero, sum_const_zero] })
          (λ a b₁ b₂, by simp only [sum, right_distrib, single_add, finset.sum_add_distrib]),
      ..fin_fn.has_add α β,
      ..fin_fn.has_mul α β }

  instance [decidable_eq α] [decidable_eq β] [add_comm_monoid α] [comm_ring β] : comm_ring (fin_fn α β) :=
    { ..fin_fn.add_comm_group α β,
      ..fin_fn.comm_monoid α β,
      ..fin_fn.distrib α β }

  instance [decidable_eq α] [decidable_eq β] [add_comm_monoid α] [half_ring β] : half_ring (fin_fn α β) :=
    { half := fin_fn.single 0 ½,
      one_is_two_halves := ext (λ a, begin
        show ite (0 = a) (1 : β) 0 = ite (0 = a) ½ 0 + ite (0 = a) ½ 0,
        by_cases h : 0 = a; simp only [if_pos, if_false, h],
        from half_ring.one_is_two_halves _,
        from (add_zero 0).symm,
      end),
      ..fin_fn.comm_ring _ β }

end group_instances

end fin_fn

#lint-
