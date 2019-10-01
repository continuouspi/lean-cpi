import data.cpi.species.basic
import order.lex_like

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi

variable {ω : environment}

open species.whole

/- So there's some pretty questionable decisions going on here, so it's worth
   exploring why this is implemented how it is:

    - species.le uses induction rather than recursive functions, as otherwise
      we do not get equation lemmas (which make it rather hard to actually see
      what's going on later on).

    - As a result, we define `A < B` as `species.le A B && A /= B`, rather than
      ¬species.le B A). This is normally fine - we can generally prove things
      other ways, but is a little odd.

    - Totality makes use of the species.eq_decidable, instead of
      lt_or_eq_of_le (again, due to how A<B is defined). It doesn't really
      matter, as neither are computable, but worth noting.

   Yeah, this whole thing is rather ugly. Sorry! -/

private noncomputable def species.eq_decidable {Γ : context ω} {k} (A B : whole k Γ) :
  decidable (A = B) := begin
  induction A,

  case nil { cases B; simp only []; apply_instance },
  case apply : _ n D as {
    cases B; simp only []; try { apply_instance },
    case apply : n' D' as' {
      cases (by apply_instance : decidable (n = n')),
      case is_true : h { subst h, simp, apply_instance },
      case is_false : h { from is_false (λ x, h x.left) }
    }
  },
  case parallel : _ A₁ A₂ ih_1 ih_2 {
    cases B; simp only []; try { apply_instance },
    case parallel : B₁ B₂ { from @and.decidable _ _ (ih_1 B₁) (ih_2 B₂) }
  },
  case restriction : _ M A ih {
    cases B; simp only []; try { apply_instance },
    case restriction : M' B {
      cases (by apply_instance : decidable (M = M')),
      case is_true : h { subst h, simp, from ih B },
      case is_false : h { from decidable.is_false (λ x, h x.left) }
     }
  },
  case choice : _ As ih {
    cases B; simp only []; try { apply_instance },
    case choice : As' { from ih As' }
  },
  case whole.empty { cases B; simp only []; apply_instance },
  case whole.cons : _ f π A As ih_a ih_as {
    cases B; simp only []; try { apply_instance },
    case whole.cons : f' π' A' As' {
      have h : decidable (prefix_expr.wrap.intro π = prefix_expr.wrap.intro π'),
        apply_instance,

      cases h,
      case is_false : p {
        from is_false (λ x, begin
          simp only [] at p,
          have : f = f' ∧ π == π' := ⟨ x.left, x.right.left ⟩,
          contradiction
        end)
      },
      case is_true : p {
        simp only [] at p,
        have : f = f' := p.left, subst this,
        simp [p],

        from @and.decidable _ _ (ih_a A') (ih_as As')
      }
    }
  }
end

noncomputable instance species.whole.decidable_eq {Γ : context ω} {k} :
  decidable_eq (whole k Γ) := species.eq_decidable

private structure pand {α : Prop} (β : α → Prop) : Prop :=
mk :: (fst : α) (snd : β fst)

notation `Σ∧` binders `, ` r:(scoped p, pand p) := r

protected def species.le : ∀ {Γ : context ω} {k}, whole k Γ → whole k Γ → Prop :=
λ Γ k A B, begin
  induction A,

  case nil { from true },
  case apply : Γ n D as {
    cases B,
    case nil { from false },
    case apply : n' D' as' {
      from n < n' ∨ (Σ∧ (H : n = n')
                     , D < (by { rw ← H at D', from D'})
                     ∨ (D = (by { rw ← H at D', from D'}) ∧ as.val ≤ as'.val))
    },
    case choice { from true },
    case parallel { from true },
    case restriction { from true },
  },
  case choice : Γ As ih {
    cases B,
    case nil { from false },
    case apply { from false },
    case choice : Bs { from ih Bs },
    case parallel { from true },
    case restriction { from true },
  },
  case parallel : Γ A A' ih ih' {
    cases B,
    case nil { from false },
    case apply { from false },
    case choice { from false },
    case parallel : B B' { from (A ≠ B ∧ ih B) ∨ (A = B ∧ ih' B') },
    case restriction { from true },
  },
  case restriction : Γ M A ih {
    cases B,
    case nil { from false },
    case apply { from false },
    case choice { from false },
    case parallel { from false },
    case restriction : N B {
      from M < N ∨ Σ∧ (H : M = N), ih (by { rw ← H at B, from B })
    },
  },

  case whole.empty { from true },
  case whole.cons : Γ f π₁ A As iha ihas {
    cases B,
    case whole.empty { from false },
    case whole.cons : f' π₂ B Bs {
      from prefix_expr.wrap.intro π₁ < prefix_expr.wrap.intro π₂ ∨
        Σ∧ (H : prefix_expr.wrap.intro π₁ = prefix_expr.wrap.intro π₂), begin
          simp at H, rw ← H.left at B,
          from (A ≠ B ∧ iha B) ∨ (A = B ∧ ihas Bs)
        end
    }
  }
end

protected theorem species.le_refl : ∀ {Γ : context ω} {k} (A : whole k Γ), species.le A A
| ._ ._ nil := true.intro
| ._ ._ (apply D as) := or.inr ⟨ rfl, or.inr ⟨ rfl, le_refl as.val ⟩ ⟩
| ._ ._ (Σ# As) := species.le_refl As
| ._ ._ (A |ₛ B) := or.inr ⟨ rfl, species.le_refl B ⟩
| ._ ._ (ν(M) A) := or.inr ⟨ rfl, species.le_refl A ⟩
| ._ ._ empty := true.intro
| ._ ._ (cons π A As) := or.inr ⟨ rfl, or.inr ⟨ rfl, species.le_refl As ⟩ ⟩

protected theorem species.le_antisymm :
  ∀ {Γ : context ω} {k} (A B : whole k Γ), species.le A B → species.le B A → A = B
| ._ ._ nil nil _ _ := rfl
| ._ ._ (@apply _ _ n D as) (apply D' as') ab ba :=
  match ab, ba with
  | or.inl lt, or.inl lt' := false.elim (lt_asymm lt lt')
  | or.inl lt, or.inr ⟨ eq, re ⟩ := false.elim (ne_of_lt lt (symm eq))
  | or.inr ⟨ eq, re ⟩, or.inl lt := false.elim (ne_of_lt lt (symm eq))
  | or.inr ⟨ eq, re ⟩, or.inr ⟨ _, re' ⟩ := begin
      clear _match, cases eq, simp,
      from match re, re' with
      | or.inl lt, or.inl lt' := false.elim (lt_asymm lt lt')
      | or.inl lt, or.inr ⟨ eq, re ⟩ := false.elim (ne_of_lt lt (symm eq))
      | or.inr ⟨ eq, re ⟩, or.inl lt := false.elim (ne_of_lt lt (symm eq))
      | or.inr ⟨ eq, le ⟩, or.inr ⟨ _, le' ⟩ := ⟨ eq, subtype.eq (le_antisymm le le') ⟩
      end
    end
  end
| ._ ._ (Σ# As) (Σ# Bs) ab ba :=
  by { simp only [], from species.le_antisymm As Bs ab ba }
| ._ ._ (A |ₛ B) (A' |ₛ B') ab ba :=
  match ab, ba with
  | or.inl ⟨ neq, le ⟩, or.inl ⟨ _, le' ⟩ :=
    false.elim (neq (species.le_antisymm A A' le le'))
  | or.inl ⟨ neq, _ ⟩, or.inr ⟨ eq, _ ⟩ := false.elim (neq (symm eq))
  | or.inr ⟨ eq, _ ⟩, or.inl ⟨ neq, _ ⟩ := false.elim (neq (symm eq))
  | or.inr ⟨ eq, lt ⟩, or.inr ⟨ _, lt' ⟩ :=
    by { simp [eq], from species.le_antisymm B B' lt lt' }
  end
| ._ ._ (ν(M) A) (ν(N) B) ab ba :=
  match ab, ba with
  | or.inl lt, or.inl lt' := false.elim (lt_asymm lt lt')
  | or.inl lt, or.inr ⟨ eq, _ ⟩ := false.elim (ne_of_lt lt (symm eq))
  | or.inr ⟨ eq, _ ⟩, or.inl lt := false.elim (ne_of_lt lt (symm eq))
  | or.inr ⟨ eq, ihl ⟩, or.inr ⟨ _, ihr ⟩ := begin
      clear _match, subst eq, simp,
      from species.le_antisymm A B ihl ihr
    end
  end

| ._ ._ empty empty _ _ := rfl
| ._ ._ (cons π₁ A As) (cons π₂ B Bs) ab ba :=
  match ab, ba with
  | or.inl lt, or.inl lt' := false.elim (lt_asymm lt lt')
  | or.inl lt, or.inr ⟨ eq, _ ⟩ := false.elim (ne_of_lt lt (symm eq))
  | or.inr ⟨ eq, _ ⟩, or.inl lt := false.elim (ne_of_lt lt (symm eq))
  | or.inr ⟨ eq, re ⟩, or.inr ⟨ _, re' ⟩ := begin
      clear _match, cases eq, simp,
      from match re, re' with
      | or.inl ⟨ neq, le ⟩, or.inl ⟨ _, le' ⟩ :=
        false.elim (neq (species.le_antisymm A B le le'))
      | or.inl ⟨ neq, le ⟩, or.inr ⟨ eq, _ ⟩ := false.elim (neq (symm eq))
      | or.inr ⟨ eq, _ ⟩, or.inl ⟨ neq, le ⟩ := false.elim (neq (symm eq))
      | or.inr ⟨ eq, le ⟩, or.inr ⟨ eq', le' ⟩ :=
        ⟨ eq, species.le_antisymm _ _ le le' ⟩
      end
    end
  end

| ._ ._ nil (apply _ _) _ f := false.elim f
| ._ ._ nil (Σ# _) _ f := false.elim f
| ._ ._ nil (_ |ₛ _) _ f := false.elim f
| ._ ._ nil (ν(_) _) _ f := false.elim f
| ._ ._ (apply _ _) nil f _ := false.elim f
| ._ ._ (apply _ _) (Σ# _) _ f := false.elim f
| ._ ._ (apply _ _) (_ |ₛ _) _ f := false.elim f
| ._ ._ (apply _ _) (ν(_) _) _ f := false.elim f
| ._ ._ (Σ# _) nil f _ := false.elim f
| ._ ._ (Σ# _) (apply _ _) f _ := false.elim f
| ._ ._ (Σ# _) (_ |ₛ _) _ f := false.elim f
| ._ ._ (Σ# _) (ν(_) _) _ f := false.elim f
| ._ ._ (_ |ₛ _) nil f _ := false.elim f
| ._ ._ (_ |ₛ _) (apply _ _) f _ := false.elim f
| ._ ._ (_ |ₛ _) (Σ# _) f _ := false.elim f
| ._ ._ (_ |ₛ _) (ν(_) _) _ f := false.elim f
| ._ ._ (ν(_) _) nil f _ := false.elim f
| ._ ._ (ν(_) _) (apply _ _) f _ := false.elim f
| ._ ._ (ν(_) _) (Σ# _) f _ := false.elim f
| ._ ._ (ν(_) _) (_ |ₛ _) f _ := false.elim f
| ._ ._ (cons _ _ _) empty f _ := false.elim f
| ._ ._ empty (cons _ _ _) _ f := false.elim f

private lemma lt_not_eq {Γ : context ω} :
  ∀ {A B C : species Γ}, species.le A B → species.le B C → A ≠ B → A ≠ C
| A B C lab lbc ab (eq.refl _) := ab (species.le_antisymm A B lab lbc)

protected theorem species.le_trans :
  ∀ {Γ : context ω} {k} (A B C : whole k Γ), species.le A B → species.le B C → species.le A C
| ._ ._ nil _ _ _ _ := true.intro

| ._ ._ (apply D as) (apply D₂ bs) (apply D₃ cs) ab bc :=
  match ab, bc with
  | or.inl lt, or.inl lt' := or.inl (lt_trans lt lt')
  | or.inl lt, or.inr ⟨ eq, _ ⟩ := or.inl (eq ▸ lt)
  | or.inr ⟨ eq, _ ⟩, or.inl lt := or.inl (symm eq ▸ lt)

  | or.inr ⟨ eq, re ⟩, or.inr ⟨ eq', re' ⟩ := begin
      clear _match, cases eq, cases eq',
      from or.inr ⟨ rfl, match re, re' with
      | or.inl lt, or.inl lt' := or.inl (lt_trans lt lt')
      | or.inl lt, or.inr ⟨ eq, _ ⟩ := or.inl (eq ▸ lt)
      | or.inr ⟨ eq, _ ⟩, or.inl lt := or.inl (symm eq ▸ lt)
      | or.inr ⟨ eq, le ⟩, or.inr ⟨ eq', le' ⟩ :=
        or.inr ⟨ trans eq eq', le_trans le le' ⟩
      end ⟩
    end
  end
| ._ ._ (apply D as) _ (Σ# _) _ _ := true.intro
| ._ ._ (apply D as) _ (_ |ₛ _) _ _ := true.intro
| ._ ._ (apply D as) _ (ν(_)_) _ _ := true.intro

| ._ ._ (Σ# As) (Σ# Bs) (Σ# Cs) ab bc := species.le_trans As Bs Cs ab bc
| ._ ._ (Σ# As) _ (_ |ₛ _) _ _ := true.intro
| ._ ._ (Σ# As) _ (ν(_)_) _ _ := true.intro

| ._ ._ (A₁ |ₛ B₁) (A₂ |ₛ B₂) (A₃ |ₛ B₃) ab bc :=
  match ab, bc with
  | or.inl ⟨ neq, le ⟩, or.inl ⟨ neq', le' ⟩ :=
      or.inl ⟨ lt_not_eq le le' neq, species.le_trans _ _ _ le le' ⟩
  | or.inl lt, or.inr ⟨ eq, _ ⟩ := or.inl (eq ▸ lt)
  | or.inr ⟨ eq, _ ⟩, or.inl lt := or.inl (symm eq ▸ lt)
  | or.inr ⟨ eq, lt ⟩, or.inr ⟨ eq', lt' ⟩ :=
    or.inr ⟨ trans eq eq', species.le_trans _ _ _ lt lt' ⟩
  end
| ._ ._ (A₁ |ₛ B₁) _ (ν(_)_) _ _ := true.intro

| ._ ._ (ν(M₁) A₁) (ν(M₂) A₂) (ν(M₃) A₃) ab bc :=
  match ab, bc with
  | or.inl lt, or.inl lt' := or.inl (lt_trans lt lt')
  | or.inl lt, or.inr ⟨ eq, _ ⟩ := or.inl (eq ▸ lt)
  | or.inr ⟨ eq, _ ⟩, or.inl lt := or.inl (symm eq ▸ lt)
  | or.inr ⟨ eq, lt ⟩, or.inr ⟨ eq', lt' ⟩ :=
    by { clear _match, subst eq, subst eq', from or.inr ⟨ rfl, species.le_trans _ _ _ lt lt' ⟩ }
  end

| ._ ._ empty _ _ _ _ := true.intro
| ._ ._ (cons π₁ A₁ As₁) (cons π₂ A₂ As₂) (cons π₃ A₃ As₃) ab bc :=
  match ab, bc with
  | or.inl lt, or.inl lt' := or.inl (lt_trans lt lt')
  | or.inl lt, or.inr ⟨ eq, _ ⟩ := or.inl (eq ▸ lt)
  | or.inr ⟨ eq, _ ⟩, or.inl lt := or.inl (symm eq ▸ lt)

  | or.inr ⟨ eq, re ⟩, or.inr ⟨ eq', re' ⟩ := begin
      clear _match, cases eq, cases eq',
      from or.inr ⟨ rfl, match re, re' with
      | or.inl ⟨ neq, le ⟩, or.inl ⟨ neq', le' ⟩ :=
        or.inl ⟨ lt_not_eq le le' neq, species.le_trans _ _ _ le le' ⟩
      | or.inl lt, or.inr ⟨ eq, _ ⟩ := or.inl (eq ▸ lt)
      | or.inr ⟨ eq, _ ⟩, or.inl lt := or.inl (symm eq ▸ lt)
      | or.inr ⟨ eq, le ⟩, or.inr ⟨ eq', le' ⟩ :=
        or.inr ⟨ trans eq eq', species.le_trans _ _ _ le le' ⟩
      end ⟩
    end
  end

-- All the impossible cases
| ._ ._ (apply _ _) nil _ f _ := false.elim f
| ._ ._ (Σ# _) nil _ f _ := false.elim f
| ._ ._ (_ |ₛ _) nil _ f _ := false.elim f
| ._ ._ (ν(_) _) nil _ f _ := false.elim f
| ._ ._ _ (Σ# _) (apply _ _) _ f := false.elim f
| ._ ._ _ (_ |ₛ _) (Σ# _) _ f := false.elim f
| ._ ._ _ (ν(M) _) (Σ# _) _ f := false.elim f
| ._ ._ (cons _ _ _) empty _ f _ := false.elim f
| ._ ._ _ (cons _ _ _) empty _ f := false.elim f

protected theorem species.le_total :
  ∀ {Γ : context ω} {k} (A B : whole k Γ), species.le A B ∨ species.le B A
| ._ ._ nil _ := or.inl true.intro
| ._ ._ _ nil := or.inr true.intro

| ._ ._ (@apply _ _ m D as) (@apply _ _ n D' bs) :=
  match le_total m n with
  | or.inl le :=
    match lt_or_eq_of_le le with
    | or.inl lt := or.inl (or.inl lt)
    | or.inr eq := begin
        clear _match _match, cases eq,
        from or.imp (λ h, or.inr ⟨ eq, h ⟩) (λ h, or.inr ⟨ symm eq, h ⟩)
          (order.lex_like.le_total D D' as.val bs.val)
      end
    end
  | or.inr le :=
    match lt_or_eq_of_le le with
    | or.inl lt := or.inr (or.inl lt)
    | or.inr eq := begin
        clear _match _match, cases (symm eq),
        from or.imp (λ h, or.inr ⟨ eq, h ⟩) (λ h, or.inr ⟨ symm eq, h ⟩)
          (order.lex_like.le_total D D' as.val bs.val)
      end
    end
  end
| ._ ._ (apply D as) (Σ# _) := or.inl true.intro
| ._ ._ (apply D as) (_ |ₛ _) := or.inl true.intro
| ._ ._ (apply D as) (ν(_) _) := or.inl true.intro

| ._ ._ (Σ# As) (apply _ _) := or.inr true.intro
| Γ ._ (Σ# As) (Σ# Bs) := species.le_total As Bs
| ._ ._ (Σ# As) (_ |ₛ _) := or.inl true.intro
| ._ ._ (Σ# As) (ν(_) _) := or.inl true.intro

| ._ ._ (A |ₛ B) (apply _ _) := or.inr true.intro
| ._ ._ (A |ₛ B) (Σ# _) := or.inr true.intro
| Γ ._ (A |ₛ B) (A' |ₛ B') :=
  if h : A = A' then
    or.imp (λ le, or.inr ⟨ h, le ⟩) (λ le, or.inr ⟨ symm h, le ⟩)
      (species.le_total B B')
  else
    or.imp (λ le, or.inl ⟨ h, le ⟩) (λ le, or.inl ⟨ ne.symm h, le ⟩)
      (species.le_total A A')
| ._ ._ (A |ₛ B) (ν(_) _) := or.inl true.intro

| ._ ._ (ν(M) A) (apply _ _ ) := or.inr true.intro
| ._ ._ (ν(M) A) (Σ# _) := or.inr true.intro
| ._ ._ (ν(M) A) (_ |ₛ _) := or.inr true.intro
| Γ ._ (ν(M) A) (ν(N) B) :=
  match le_total M N with
  | or.inl le :=
    match lt_or_eq_of_le le with
    | or.inl lt := or.inl (or.inl lt)
    | or.inr eq :=
      or.imp (λ le, or.inr ⟨ eq, le ⟩) (λ le, or.inr ⟨ symm eq, le ⟩)
        (by { clear _match _match, cases eq, from species.le_total A B })
    end
  | or.inr le :=
    match lt_or_eq_of_le le with
    | or.inl lt := or.inr (or.inl lt)
    | or.inr eq := begin
        clear _match _match, cases (symm eq),
        from or.imp (λ le, or.inr ⟨ rfl, le ⟩) (λ le, or.inr ⟨ rfl, le ⟩)
          (species.le_total A B)
      end
    end
  end

| ._ ._ empty _ := or.inl true.intro
| ._ ._ _ empty := or.inr true.intro

| Γ ._ (cons π₁ A As) (cons π₂ B Bs) :=
  match le_total (prefix_expr.wrap.intro π₁) (prefix_expr.wrap.intro π₂) with
  | or.inl le :=
    match lt_or_eq_of_le le with
    | or.inl lt := or.inl (or.inl lt)
    | or.inr eq := begin
        clear _match _match, cases eq,
        from if h : A = B then
          or.imp
            (λ le, or.inr ⟨ rfl, or.inr ⟨ h, le ⟩ ⟩ )
            (λ le, or.inr ⟨ rfl, or.inr ⟨ symm h, le ⟩ ⟩)
            (species.le_total As Bs)
        else
          or.imp
            (λ le, or.inr ⟨ rfl, or.inl ⟨ h, le ⟩ ⟩)
            (λ le, or.inr ⟨ rfl, or.inl ⟨ ne.symm h, le ⟩ ⟩)
            (species.le_total A B)
      end
    end
  | or.inr le :=
    match lt_or_eq_of_le le with
    | or.inl lt := or.inr (or.inl lt)
    | or.inr eq := begin
        clear _match _match, cases (symm eq),
        from if h : A = B then
          or.imp
            (λ le, or.inr ⟨ rfl, or.inr ⟨ h, le ⟩ ⟩ )
            (λ le, or.inr ⟨ rfl, or.inr ⟨ symm h, le ⟩ ⟩)
            (species.le_total As Bs)
        else
          or.imp
            (λ le, or.inr ⟨ rfl, or.inl ⟨ h, le ⟩ ⟩)
            (λ le, or.inr ⟨ rfl, or.inl ⟨ ne.symm h, le ⟩ ⟩)
            (species.le_total A B)
      end
    end
  end

section
set_option eqn_compiler.lemmas false
private noncomputable def species.le_decidable :
  ∀ {Γ : context ω} {k} (A B : whole k Γ), decidable (species.le A B)
| ._ ._ nil _ := decidable.true

| ._ ._ (@apply _ _ m D as) (@apply _ _ n D' bs) :=
  if eqm : m = n then
    begin
      cases eqm,
      have : decidable (D < D' ∨ D = D' ∧ as.val ≤ bs.val), apply_instance,
      cases this,
      case is_true { from is_true (or.inr ⟨ rfl, this ⟩) },
      case is_false {
        from is_false (λ x,
          match x with
          | or.inl lt := lt_irrefl m lt
          | or.inr ⟨ _, h ⟩ := this h
          end)
      }
    end
  else if lt : m < n then
    is_true (or.inl lt)
  else
    is_false (λ x,
      match x with
      | or.inl lt' := lt lt'
      | or.inr ⟨ eq', _ ⟩ := eqm eq'
      end)
| ._ ._ (apply D as) nil := decidable.false
| ._ ._ (apply D as) (Σ# _) := decidable.true
| ._ ._ (apply D as) (_ |ₛ _) := decidable.true
| ._ ._ (apply D as) (ν(_) _) := decidable.true

|  Γ ._ (Σ# As) (Σ# Bs) := species.le_decidable As Bs
| ._ ._ (Σ# As) nil := decidable.false
| ._ ._ (Σ# As) (apply _ _) := decidable.false
| ._ ._ (Σ# As) (_ |ₛ _) := decidable.true
| ._ ._ (Σ# As) (ν(_) _) := decidable.true

| ._ ._ (A |ₛ B) nil := decidable.false
| ._ ._ (A |ₛ B) (apply _ _) := decidable.false
| ._ ._ (A |ₛ B) (Σ# _) := decidable.false
|  Γ ._ (A |ₛ B) (A' |ₛ B') :=
  if eq : A = A' then
    match species.le_decidable B B' with
    | is_true le := is_true (or.inr ⟨ eq, le ⟩)
    | is_false nle := is_false (λ x, by { cases x; cases x; contradiction })
    end
  else
    match species.le_decidable A A' with
    | is_true le := is_true (or.inl ⟨ eq, le ⟩)
    | is_false nle := is_false (λ x, by { cases x; cases x; contradiction })
    end
| ._ ._ (A |ₛ B) (ν(_) _) := decidable.true

| ._ ._ (ν(M) A) nil := decidable.false
| ._ ._ (ν(M) A) (apply _ _) := decidable.false
| ._ ._ (ν(M) A) (Σ# _) := decidable.false
| ._ ._ (ν(M) A) (_ |ₛ _) := decidable.false
|  Γ ._ (ν(M) A) (ν(N) B) :=
  if eq : M = N then
    begin
      cases eq,
      cases (species.le_decidable A B) with h,
      case is_true { from is_true (or.inr ⟨ eq, h ⟩) },
      case is_false {
        from is_false (λ x,
          match x with
          | or.inl lt := lt_irrefl M lt
          | or.inr ⟨ _, le ⟩ := by contradiction
          end)
      }
    end
  else if lt : M < N then
    is_true (or.inl lt)
  else
    is_false (λ x,
      match x with
      | or.inl x := by contradiction
      | or.inr y := by { cases y, contradiction }
      end)

| ._ ._ empty _ := decidable.true

| ._ ._ (cons π₁ A As) empty := decidable.false
|  Γ ._ (cons π₁ A As) (cons π₂ B Bs) :=
  if eqπ : prefix_expr.wrap.intro π₁ = prefix_expr.wrap.intro π₂ then
    begin
      cases eqπ,
      from if eqa : A = B then
        match species.le_decidable As Bs with
        | is_true le := is_true (or.inr ⟨ eqπ, or.inr ⟨ eqa, le ⟩ ⟩)
        | is_false nle := is_false (λ x,
          match x with
          | or.inl lt := lt_irrefl _ lt
          | or.inr ⟨ _, or.inl ⟨ neq, _ ⟩ ⟩ := neq eqa
          | or.inr ⟨ _, or.inr ⟨ _, le ⟩ ⟩ := nle le
          end)
        end
      else
        match species.le_decidable A B with
        | is_true le := is_true (or.inr ⟨ eqπ, or.inl ⟨ eqa, le ⟩ ⟩)
        | is_false nle := is_false (λ x,
          match x with
          | or.inl lt := lt_irrefl _ lt
          | or.inr ⟨ _, or.inl ⟨ _, le ⟩ ⟩ := nle le
          | or.inr ⟨ _, or.inr ⟨ eq, _ ⟩ ⟩ := eqa eq
          end)
        end
    end
  else if lt : prefix_expr.wrap.intro π₁ < prefix_expr.wrap.intro π₂ then
    is_true (or.inl lt)
  else
    is_false (λ x,
      match x with
      | or.inl lt' := lt lt'
      | or.inr y := by { cases y, contradiction }
      end)
end

noncomputable instance species.whole.decidable_linear_order {Γ : context ω} {k} :
  decidable_linear_order (whole k Γ) :=
  { le := species.le,
    le_refl := species.le_refl,
    le_trans := species.le_trans,
    le_antisymm := species.le_antisymm,
    le_total := species.le_total,
    decidable_le := species.le_decidable,
    decidable_eq := species.eq_decidable }

end cpi

#sanity_check
