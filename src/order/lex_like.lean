/- Various utilities for proving properties of orderings. -/

namespace order

/-- Show le_total for a basic lexiographic-like order. -/
protected lemma lex_like.le_total
    {α β : Type*} [linear_order α] [linear_order β]
    (a a' : α) (b b' : β)
  : (a < a' ∨ (a = a' ∧ b ≤ b')) ∨ (a' < a ∨ (a' = a ∧ b' ≤ b))
  := begin
    cases le_total a a',
    case or.inl : a_le {
      cases lt_or_eq_of_le a_le,
      case or.inl : lt { from or.inl (or.inl lt) },
      case or.inr : eq {
        cases eq,
        from or.imp (λ h, or.inr ⟨ eq, h ⟩) (λ h, or.inr ⟨ symm eq, h ⟩)
          (le_total b b')
      }
    },
    case or.inr : b_le_a {
      cases lt_or_eq_of_le b_le_a,
      case or.inl : lt { from or.inr (or.inl lt) },
      case or.inr : eq {
        cases eq,
        from or.imp (λ h, or.inr ⟨ eq, h ⟩) (λ h, or.inr ⟨ symm eq, h ⟩)
          (le_total b b')
      }
    }
  end

end order
