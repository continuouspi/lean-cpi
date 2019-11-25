import data.fin.pi_order data.option.order data.pand

namespace cpi

/-- An affinity network.

    This is composed of $arity$ names, and a partial function `f' which defines
    the affinities between elements of this matrix.
-/
@[derive decidable_eq]
structure affinity (ℍ : Type) := intro ::
  (arity : ℕ)
  (f : fin arity → fin arity → option ℍ)
  (symm : ∀ x y, f x y = f y x)

variables {ℍ : Type}

/- Just show that affinity networks form a decidable linear order. -/
section ordering
  /-- Affinity networks take a lexiographic ordering, with the arity and mapping
      function. -/
  def affinity.le [partial_order ℍ] : affinity ℍ → affinity ℍ → Prop
  | ⟨ a, f, sf ⟩ ⟨ b, g, sg ⟩ :=
    a < b ∨ (Σ∧ (x : a = b), cast (congr_arg (λ x, fin x → fin x → option ℍ) x) f ≤ g)

  protected theorem affinity.le_refl [partial_order ℍ] :
    ∀ (M : affinity ℍ), affinity.le M M
  | ⟨ a, f, _ ⟩ := or.inr ⟨ rfl, le_refl f ⟩

  protected theorem affinity.le_trans [partial_order ℍ] :
    ∀ (M N O : affinity ℍ), affinity.le M N → affinity.le N O → affinity.le M O
  | ⟨ a, f, sf ⟩ ⟨ b, g, sg ⟩ ⟨ c, h, sh ⟩ (or.inl lt) (or.inl lt')
    := or.inl (lt_trans lt lt')
  | ⟨ a, f, sf ⟩ ⟨ _, g, sg ⟩ ⟨ _, h, sh ⟩ (or.inl lt) (or.inr ⟨ eq.refl b, le ⟩)
    := or.inl lt
  | ⟨ _, f, sf ⟩ ⟨ _, g, sg ⟩ ⟨ c, h, sh ⟩ (or.inr ⟨ eq.refl a, le ⟩) (or.inl lt)
    := or.inl lt
  | ⟨ _, f, sf ⟩ ⟨ _, g, sg ⟩ ⟨ _, h, sh ⟩ (or.inr ⟨ eq.refl _, le ⟩) (or.inr ⟨ eq.refl a, le' ⟩)
    := or.inr ⟨ rfl, le_trans le le' ⟩

  protected theorem affinity.le_antisymm [partial_order ℍ] :
    ∀ (M N : affinity ℍ), affinity.le M N → affinity.le N M → M = N
  | ⟨ a, f, sf ⟩ ⟨ b, g, sg ⟩ (or.inl lt) (or.inl lt')
    := false.elim (lt_asymm lt lt')
  | ⟨ a, f, sf ⟩ ⟨ _, g, sg ⟩ (or.inl lt) (or.inr ⟨ eq.refl b, le ⟩)
    := false.elim (lt_irrefl _ lt)
  | ⟨ _, f, sf ⟩ ⟨ _, g, sg ⟩ (or.inr ⟨ eq.refl a, le ⟩) (or.inl lt)
    := false.elim (lt_irrefl _ lt)
  | ⟨ _, f, sf ⟩ ⟨ _, g, sg ⟩ (or.inr ⟨ eq.refl _, le ⟩) (or.inr ⟨ eq.refl a, le' ⟩)
    := by { simp, from le_antisymm le le' }

  protected theorem affinity.le_total [linear_order ℍ] :
    ∀ (M N : affinity ℍ), affinity.le M N ∨ affinity.le N M
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

  /-- A decision procedure for affinity network comparison. -/
  protected def affinity.decidable_le [decidable_linear_order ℍ] :
    ∀ (M N : affinity ℍ), decidable (affinity.le M N)
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

  instance affinity.linear_order [linear_order ℍ] : linear_order (affinity ℍ) :=
    { le := affinity.le,
      le_refl := affinity.le_refl,
      le_trans := affinity.le_trans,
      le_antisymm := affinity.le_antisymm,
      le_total := affinity.le_total }

  instance [decidable_linear_order ℍ] : decidable_linear_order (affinity ℍ) :=
    { decidable_eq := affinity.decidable_eq ℍ,
      decidable_le := affinity.decidable_le,
      ..affinity.linear_order }

end ordering

end cpi

#lint -
