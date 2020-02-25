import data.cpi.species.normalise data.cpi.species.prime

namespace cpi
namespace species
namespace normalise

variables {ℍ : Type} {ω : context}
open_locale normalise

/-- Determine if normalising a species or choice yields a list of primes. Note
    that choices are inherently prime. -/
@[reducible]
def to_kind' : ∀ (k : kind), kind' ℍ k
| kind.species := kind'.atom
| kind.choices := kind'.choices

axiom normalise_atom :
  ∀ {k} {Γ} {A : whole ℍ ω k Γ}
  , atom (to_kind' k) A → normalise A = A

lemma normalise_nil {Γ} : normalise (@nil ℍ ω Γ) = nil
  := by unfold normalise normalise_to parallel.from_list

/-- Show that any atomic species must be prime. -/
lemma atom_prime : ∀ {Γ} (A : species ℍ ω Γ), atom kind'.atom A → prime A
| Γ A atomA := ⟨ λ isNil, begin
    unfold_projs at isNil, unfold equiv at isNil,
    rw [normalise_atom atomA] at isNil, subst isNil,
    rw normalise_nil at atomA, cases atomA,
  end, λ B₁ B₂ equ, begin
    unfold_projs at equ, unfold equiv at equ,
    rw [normalise_atom atomA] at equ, subst equ,

    unfold normalise normalise_to at atomA,
    rcases dB₁ : normalise_to B₁ with ⟨ nB₁, eqB₁, atomB₁ ⟩, rw dB₁ at atomA,
    rcases dB₂ : normalise_to B₂ with ⟨ nB₂, eqB₂, atomB₂ ⟩, rw dB₂ at atomA,
    unfold normalise_to._match_2 normalise_to._match_1 at atomA,

    cases nB₁,
    case list.nil {
      -- nB₁ is nil, then B₁ ≈ nil
      simp only [list.nil_append] at atomA,
      suffices : parallel.from_list (normalise_to B₁).fst = normalise nil,
        from or.inl this,

      rw [dB₁, normalise_nil],
      from rfl,
    },

    case list.cons : nB₁' nBs₁ {
      simp only [list.cons_append] at atomA,
      cases h : nBs₁ ++ nB₂,
      case list.nil {
        -- nBs₁ ++ nB₂ is nil, then B₂ is nil, thus B₁ ≈ nil
        suffices : parallel.from_list (normalise_to B₂).fst = normalise nil,
          from or.inr this,

        simp only [dB₂, normalise_nil, (list.append_eq_nil.mp h).2],
        from rfl,
      },

      case list.cons {
        -- This would mean we have atom (nB₁' |ₛ parallel.from_list (nBs₁ ++ nB₂)),
        -- which is impossible.
        rw h at atomA, cases atomA,
      }
    }
  end ⟩

end normalise

end species
end cpi

#lint-
