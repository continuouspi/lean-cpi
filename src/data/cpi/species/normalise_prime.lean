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

private lemma partition_restriction_atom {Γ} (M : affinity ℍ) :
  ∀ (As : list (species ℍ ω (context.extend (M.arity) Γ)))
    (C : species ℍ ω (context.extend (M.arity) Γ))
    (h : ∀ A ∈ As, normalise.atom normalise.kind'.atom A ∧ level.zero ∈ A)
  , partition_restriction M As C (λ x mem, (h x mem).1)
  = ⟨ As, [], equiv.parallel_nil₂, h, λ x mem, by cases mem ⟩
| [] C h := begin
  simp only [partition_restriction],
  from ⟨ rfl, heq.rfl ⟩,
end
| (A::As) C h := begin
  simp only [partition_restriction],

  have h := partition_restriction_atom As (C |ₛ A)
    (λ x mem, h x (list.mem_cons_of_mem _ mem)),
  rw h, clear h,

  simp only [partition_restriction._match_1, dite],
  cases (@free_in.decidable ℍ ω _ _ level.zero A),

  case is_false : notFree {
    simp only [],
    from absurd (h A (list.mem_cons_self A _)).2 notFree,
  },

  simp only [],
  from ⟨ ⟨ rfl, rfl ⟩, heq.rfl ⟩,
end

private lemma undo_choice {Γ} (M : affinity ℍ) :
  ∀ (A : species ℍ ω (context.extend (M.arity) Γ))
    (As : list (species ℍ ω (context.extend (M.arity) Γ)))
  , atom (kind'.in_nu M) (parallel.from_list (A::As))
  → (∀ (B : whole ℍ ω kind.species (context.extend (M.arity) Γ)), B ∈ (list.cons A As) → atom kind'.atom B)
  → ∀ B ∈ (list.cons A As), normalise.atom normalise.kind'.atom B ∧ level.zero ∈ B
| A [] atomAs atomEach B mem := begin
  -- We're a singleton list, so must be nu_one.
  cases mem, case or.inr { cases mem }, subst mem,
  cases atomAs, case atom.nu_cons { cases atomEach _ (list.mem_cons_self _ _) },

  from ⟨ ‹ atom kind'.atom B ›, ‹ level.zero ∈ B › ⟩,
end
| A (A'::As) atomAs atomEach B mem := begin
  -- Similarly, we must be nu_cons.
  cases atomAs, case atom.nu_one : atomA { cases atomA },

  cases mem,
  case or.inl { subst mem, from ⟨ ‹ atom kind'.atom B ›, ‹ level.zero ∈ B › ⟩ },
  case or.inr {
    from undo_choice A' As ‹ atom (kind'.in_nu M) (parallel.from_list (A' :: As)) ›
      (λ x mem, atomEach x (list.mem_cons_of_mem _ mem))
      _ mem,
  }
end

private lemma parallel_restriction_atom {Γ} (M : affinity ℍ) :
  ∀ (A : list (species ℍ ω (context.extend (M.arity) Γ)))
    (atomA : atom (kind'.in_nu M) (parallel.from_list A))
    (atomEach : ∀ (B : whole ℍ ω kind.species (context.extend (M.arity) Γ)), B ∈ A → atom kind'.atom B)
  , parallel.from_list ((normalise_restriction M A atomEach).fst)
  = ν(M) parallel.from_list A
| As atomAs atomEach := begin
  simp only [normalise_restriction],

  cases As with A As,
  case list.nil { cases atomAs, cases atomAs_a },

  have atomLike : ∀ B ∈ (list.cons A As), normalise.atom normalise.kind'.atom B ∧ level.zero ∈ B
    := undo_choice M A As atomAs atomEach,

  rw partition_restriction_atom M (A::As) nil atomLike,
  simp only [normalise_restriction._match_2],

  rcases defB : build_restriction M (A :: As) [] atomLike _ with ⟨ As₂, eq₂, atomAs₂ ⟩,
  simp only [build_restriction] at defB,
  simp only [normalise_restriction._match_1],

  rw ← defB.1,
  from rfl,
end

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
lemma atom_prime : ∀ {Γ} {A : species ℍ ω Γ}, atom kind'.atom A → prime A
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

/-- Decompose a species into a list of prime species. -/
def prime_decompose {Γ} : species ℍ ω Γ → list (prime_species ℍ ω Γ)
| A :=
  let ⟨ As, _, atomAs ⟩ := normalise_to A in
  list.map_witness As (λ A mem, ⟨ A, atom_prime (atomAs A mem) ⟩ )

lemma prime_decompose.equiv {Γ} {A B : species ℍ ω Γ} (h : A ≈ B)
  : prime_decompose A = prime_decompose B := begin
  suffices : (normalise_to A).1 = (normalise_to B).1,
    unfold prime_decompose,
    rcases defA : normalise_to A with ⟨ A', eqA, atomA ⟩,
    rcases defB : normalise_to B with ⟨ B', eqB, atomB ⟩,
    rw [defA, defB] at this, simp only [] at this, subst this,
    from rfl,

  from equiv.normalise_to h,
end

/-- prime_decompose' on setoids. -/
def prime_decompose' {Γ} : species' ℍ ω Γ → multiset (prime_species' ℍ ω Γ)
  := begin
  refine quot.map (λ A, list.map quotient.mk (prime_decompose A)) _,

  assume A B equi,
  show (list.map quotient.mk (prime_decompose A))
     ~ (list.map quotient.mk (prime_decompose B)),

  rw prime_decompose.equiv equi,
end

lemma prime_decompose.nil {Γ} : prime_decompose (@nil ℍ ω Γ) = [] := begin
  simp only [prime_decompose],
  rcases h : normalise_to nil with ⟨ xs, eql, atom ⟩,
  simp only [normalise_to] at h, cases h, clear h,
  from rfl,
end

lemma normalise_to.parallel {Γ} (A B : species ℍ ω Γ)
  : (normalise_to (A |ₛ B)).fst = (normalise_to A).fst ++ (normalise_to B).fst := begin
  unfold normalise_to,

  rcases normalise_to A with ⟨ A', eqA, atomA' ⟩,
  rcases normalise_to B with ⟨ B', eqB, atomB' ⟩,
  from rfl,
end

lemma prime_decompose.parallel {Γ} (A B : species ℍ ω Γ)
  : prime_decompose (A |ₛ B) = prime_decompose A ++ prime_decompose B
  := begin
  unfold prime_decompose,

  have h := normalise_to.parallel A B,
  rcases normalise_to A with ⟨ A', eqA, atomA ⟩, assume h,
  rcases normalise_to B with ⟨ B', eqB, atomB ⟩, assume h,
  rcases normalise_to (A |ₛ B) with ⟨ AB', eqAB, atomAB ⟩, assume h,

  unfold prime_decompose._match_1, unfold_projs at h, clear eqA eqB eqAB A B,

  induction A' generalizing AB',
  case list.nil {
    simp only [list.append, list.nil_append, list.map_witness] at ⊢ h,
    subst h,
  },
  case list.cons : A' As' ih {
    simp only [list.append, list.cons_append, list.map_witness] at ⊢ h,
    subst h,
    simp only [list.map_witness],
    from ⟨ rfl, ih _ _ _ rfl ⟩,
  }
end

lemma prime_decompose'.nil {Γ} : prime_decompose' ⟦ @nil ℍ ω Γ ⟧ = [] := quot.sound(begin
  simp only [prime_decompose.nil],
  from refl _,
end)

lemma prime_decompose'.parallel {Γ} (A B : species ℍ ω Γ)
  : prime_decompose' ⟦A |ₛ B⟧ = prime_decompose' ⟦ A ⟧ + prime_decompose' ⟦ B ⟧
  := quot.sound (begin
    simp only [prime_decompose.parallel, list.map_append],
    from refl _,
  end)

axiom normalise_to.prime {Γ} (A : species ℍ ω Γ)
  : prime A → (normalise_to A).fst = [A]

lemma prime_decompose.prime {Γ} (A : prime_species ℍ ω Γ)
  : prime_decompose A.val = [A] := begin
  unfold prime_decompose,

  have h := normalise_to.prime A.val A.property,
  rcases normalise_to A.val with ⟨ A', eqA, atomA ⟩, assume h,

  simp only [] at h, subst h,
  unfold prime_decompose._match_1 list.map_witness,
  simp only [subtype.eta],
  from ⟨ rfl, rfl ⟩,
end

lemma prime_decompose'.prime {Γ} (A : prime_species' ℍ ω Γ)
  : prime_decompose' (prime_species.unwrap A) = [ A ]
  := begin
    rcases quot.exists_rep A with ⟨ ⟨ A, prime ⟩, eq ⟩, subst eq,

    show prime_decompose' ⟦A⟧ = ⟦ [quot.mk setoid.r ⟨A, prime⟩] ⟧,

    suffices : list.map quotient.mk (prime_decompose A) ≈ [quot.mk setoid.r ⟨A, prime⟩],
      from quot.sound this,

    rw prime_decompose.prime ⟨ A, prime ⟩,
    from refl _,
  end

end normalise
end species
end cpi

#lint-
