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

lemma normalise_nil {Γ} : normalise (@nil ℍ ω Γ) = nil
  := by unfold normalise normalise_to parallel.from_list

/-- If we have a list of species which are an atom, then it must be a singleton
    list. -/
def atom_singleton_parallel {Γ} :
  ∀ {As : list (species ℍ ω Γ)}
  , atom kind'.atom (parallel.from_list As)
  → Σ' (A : species ℍ ω Γ), As = [A]
| [] atom := by { exfalso, cases atom }
| [A] atom := ⟨ A, rfl ⟩
| (A::B::As) atom := by { exfalso, cases atom }

axiom parallel_restriction_atom {Γ} (M : affinity ℍ) :
  ∀ (A : list (species ℍ ω (context.extend (M.arity) Γ)))
    (atomA : atom (kind'.in_nu M) (parallel.from_list A))
    (atomEach : ∀ (B : whole ℍ ω kind.species (context.extend (M.arity) Γ)), B ∈ A → atom kind'.atom B)
  , parallel.from_list ((normalise_restriction M A atomEach).fst)
  = ν(M) parallel.from_list A
-- | A atom atomEach := begin
--   simp only [normalise_restriction],
-- end

lemma normalise_atom :
  ∀ {sk} {k : kind' ℍ sk} {Γ} {A : whole ℍ ω sk Γ}
  , atom k A → normalise A = A
| sk k Γ A atom := begin
  induction atom; try { assumption },

  -- The proof for this is pretty simple, and follows the same template:
  --
  --  • Induct over the child fields:
  --      rcases normalise_to A with ⟨ A', eqA, atomA ⟩ assume ih, simp only [] at ih, subst ih,
  --    We need the weird "assume ih, ..." lines to reintroduce the induction hypothesis
  --    - rcases is a little weird here.
  --  • Unfold the internal matches
  --  • Actually prove this case

  case atom.choice_cons : Γ A As atomA atomAs ihA ihAs {
    simp only [normalise, normalise_to, parallel.from_list] at ⊢ ihA ihAs,
    rcases normalise_to A with ⟨ A', eqA, atomA' ⟩,     assume ih, simp only [] at ih, subst ih,
    rcases normalise_to As with ⟨ As', eqAs, atomAs' ⟩, assume ih, simp only [] at ih, subst ih,
    simp only [normalise_to._match_1, normalise_to._match_2], clear eqA eqAs atomA' atomAs',

    cases atom_singleton_parallel atomA with A' h, subst h,
    simp only [list.cons_append, list.nil_append, parallel.from_list],

    cases As',
    case list.nil { cases atomAs, cases atomAs_a },
    from rfl,
  },

  case atom.nu_cons : Γ M A As atomA usesA atomAs ihA ihAs {
    simp only [normalise, normalise_to, parallel.from_list] at ⊢ ihA ihAs,
    rcases normalise_to A with ⟨ A', eqA, atomA' ⟩,     assume ih, simp only [] at ih, subst ih,
    rcases normalise_to As with ⟨ As', eqAs, atomAs' ⟩, assume ih, simp only [] at ih, subst ih,
    simp only [normalise_to._match_1, normalise_to._match_2], clear eqA eqAs atomA' atomAs',

    cases atom_singleton_parallel atomA with A' h, subst h,
    simp only [list.cons_append, list.nil_append, parallel.from_list],

    cases As',
    case list.nil { cases atomAs, cases atomAs_a },
    from rfl,
  },

  case atom.apply {
    simp only [normalise, normalise_to, parallel.from_list],
    from ⟨ rfl, heq.rfl, heq.rfl ⟩,
  },

  case atom.choice : Γ As atomAs ih {
    simp only [normalise, normalise_to, parallel.from_list] at ⊢ ih,
    rcases normalise_to As with ⟨ As', eqAs, atomAs' ⟩, assume ih, simp only [] at ih, subst ih,
    simp only [normalise_to._match_5], clear eqAs,
    from rfl,
  },

  case atom.restriction : Γ M A atomA ih {
    simp only [normalise, normalise_to, parallel.from_list] at ⊢ ih,
    rcases normalise_to A with ⟨ A', eqA, atomA' ⟩, assume ih, simp only [] at ih, subst ih,
    simp only [normalise_to._match_4],

    rcases h : normalise_restriction M A' atomA' with ⟨ A₂, eqA₂, atomA₂ ⟩,
    simp only [normalise_to._match_3],

    suffices : parallel.from_list (normalise_restriction M A' atomA').fst
             = ν(M) parallel.from_list A',
      rw h at this, from this,
    from parallel_restriction_atom M A' atomA atomA',
  },

  case normalise.atom.empty { simp only [normalise, normalise_to, parallel.from_list] },

  case atom.cons_nil : Γ f π As atomAs ih {
    unfold normalise, unfold1 normalise_to, simp only [normalise, normalise_to] at ih,
    rcases normalise_to As with ⟨ As', eqAs, atomAs' ⟩, assume ih, simp only [] at ih, subst ih,
    rcases defNil : normalise_to nil with ⟨ nil', eqNil, atomNil' ⟩,
    simp only [normalise_to._match_6, normalise_to._match_7],

    have : parallel.from_list nil' = nil,
    { simp only [normalise_to] at defNil,
      rw ← (psigma.mk.inj defNil).1,
      from rfl },
    from ⟨ rfl, heq.rfl, heq_of_eq this, rfl ⟩,
  },

  case atom.cons_species : Γ f π A As atomA atomAs ihA ihAs {
    simp only [normalise, normalise_to, parallel.from_list] at ⊢ ihA ihAs,
    rcases normalise_to A with ⟨ A', eqA, atomA' ⟩,     assume ih, simp only [] at ih, subst ih,
    rcases normalise_to As with ⟨ As', eqAs, atomAs' ⟩, assume ih, simp only [] at ih, subst ih,
    simp only [normalise_to._match_6, normalise_to._match_7],

    from ⟨ rfl, heq.rfl, heq.rfl, rfl ⟩,
  }
end


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
