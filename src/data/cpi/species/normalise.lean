import data.cpi.species.congruence

namespace cpi
namespace species

variables {ℍ : Type} {ω : context}
open_locale congruence

/-- Drop a binder from a species, assuming the binder is unused. -/
def drop {Γ} {k} {n} {A : whole ℍ ω k (context.extend n Γ)}
  : level.zero ∉ A → whole ℍ ω k Γ
| free := rename_with A (name.drop_var (λ l, l ∈ A) free)

lemma drop_extend {Γ} {n} {A : species ℍ ω (context.extend n Γ)} (fr : level.zero ∉ A)
  : rename name.extend (drop fr) = A
  := begin
    unfold drop,
    rw [rename_with_compose,
        name.drop_var_compose (λ l, l ∈ A) fr,
        rename_with_id]
  end

namespace normalise
  /-- A version of species.kind, but for atoms. -/
  @[nolint has_inhabited_instance]
  inductive kind' (ℍ : Type) : kind → Type
  | atom       {} : kind' kind.species
  | in_choice  {} : kind' kind.species
  | in_nu      {} : affinity ℍ → kind' kind.species
  | choices    {}: kind' kind.choices

  /-- A more restrictive kind of species. -/
  inductive atom :
    ∀ {sk : kind} (k : kind' ℍ sk) {Γ : context}
    , whole ℍ ω sk Γ → Prop

  | choice_one {Γ} {A : species ℍ ω Γ}
    : atom kind'.atom A
    → atom kind'.in_choice A
  | choice_cons {Γ} {A As : species ℍ ω Γ}
    : atom kind'.atom A
    → atom kind'.in_choice As
    → atom kind'.in_choice (A |ₛ As)

  | nu_one {Γ} (M : affinity ℍ) {A : species ℍ ω (context.extend M.arity Γ)}
    : atom kind'.atom A → level.zero ∈ A
    → atom (kind'.in_nu M) A
  | nu_cons {Γ} (M : affinity ℍ) {A As : species ℍ ω (context.extend M.arity Γ)}
    : atom kind'.atom A → level.zero ∈ A
    → atom (kind'.in_nu M) As
    → atom (kind'.in_nu M) (A |ₛ As)

  | apply {Γ} {n} (D : reference n ω) (as : vector (name Γ) n)
    : atom kind'.atom (apply D as)
  | choice {Γ} {As : choices ℍ ω Γ}
    : atom kind'.choices As
    → atom kind'.atom (Σ# As)
  | restriction {Γ} (M : affinity ℍ) {A : species ℍ ω (context.extend M.arity Γ)}
    : atom (kind'.in_nu M) A
    → atom kind'.atom (ν(M) A)

  | empty {} {Γ} : atom kind'.choices (@whole.empty ℍ ω Γ)
  | cons_nil {Γ} {f} (π : prefix_expr ℍ Γ f) {As : choices ℍ ω Γ}
    : atom kind'.choices As
    → atom kind'.choices (whole.cons π nil As)
  | cons_species {Γ} {f} (π : prefix_expr ℍ Γ f) {A : species ℍ ω (f.apply Γ)} {As : choices ℍ ω Γ}
    : atom kind'.in_choice A
    → atom kind'.choices As
    → atom kind'.choices (whole.cons π A As)

  lemma mk_choice {Γ : context} {f} (π : prefix_expr ℍ Γ f) {As : choices ℍ ω Γ}:
    ∀ (Bs : list (species ℍ ω (f.apply Γ)))
    , (∀ B ∈ Bs, atom kind'.atom B)
    → atom kind'.choices As
    → atom kind'.choices (whole.cons π (parallel.from_list Bs) As)
  | [] _ atomAs := atom.cons_nil π atomAs
  | (B::Bs) atomBs atomAs := begin
    suffices : atom kind'.in_choice (parallel.from_list (B :: Bs)),
      from atom.cons_species π this atomAs,

    induction Bs generalizing B,
    case list.nil { from atom.choice_one (atomBs B (list.mem_cons_self B _)) },
    case list.cons : B' Bs ih {
      refine atom.choice_cons (atomBs B (list.mem_cons_self B _)) _,
      from ih B' (λ x mem, atomBs x (list.mem_cons_of_mem _ mem)),
    }
  end

  /-- parallel.from_list is injective on atoms. -/
  lemma atom_parallel_inj {Γ} :
    ∀ (As Bs : list (species ℍ ω Γ))
    , parallel.from_list As = parallel.from_list Bs
    → (∀ (A : whole ℍ ω kind.species Γ), A ∈ As → atom kind'.atom A)
    → (∀ (A : whole ℍ ω kind.species Γ), A ∈ Bs → atom kind'.atom A)
    → As = Bs
  | [] [] ⟨ _ ⟩ atomA atomB := rfl
  | [] [_] ⟨ _ ⟩ atomA atomB := by cases atomB _ (list.mem_cons_self _ _)
  | [] (B::B'::Bs) eq atomA atomB := by cases eq

  | [_] [] ⟨ _ ⟩ atomA atomB := by cases atomA _ (list.mem_cons_self _ _)
  | [A] [B] ⟨ _ ⟩ atomA atomB := rfl
  | [A] (B::B'::Bs') ⟨ _ ⟩ atomA atomB := by cases atomA _ (list.mem_cons_self _ _)

  | (A::A'::As) [] eq atomA atomB := by cases eq
  | (A::A'::As) [B] ⟨ _ ⟩ atomA atomB := by cases atomB _ (list.mem_cons_self _ _)
  | (A::A'::As) (B::B'::Bs) eq atomA atomB := begin
    simp only [parallel.from_list] at eq,
    have h := atom_parallel_inj (A'::As) (B'::Bs) eq.2
      (λ x mem, atomA x (list.mem_cons_of_mem _ mem))
      (λ x mem, atomB x (list.mem_cons_of_mem _ mem)),
    rw [eq.1, h],
  end

  axiom drop_atom :
    ∀ {Γ} {sk} {k : kind' ℍ sk} {n} {A : whole ℍ ω sk (context.extend n Γ)} (h : level.zero ∉ A)
    , atom k A → atom k (drop h)
end normalise

/-- Splits the parallel component of a restriction into two parts - those
    which can be lifted out of it, and those which cannot. -/
def partition_restriction : ∀ {Γ}
    (M : affinity ℍ)
    (As : list (species ℍ ω (context.extend (M.arity) Γ)))
    (C : species ℍ ω (context.extend (M.arity) Γ))
  , (∀ A ∈ As, normalise.atom normalise.kind'.atom A)
  → Σ' (As' : list (species ℍ ω (context.extend (M.arity) Γ)))
       (Bs : list (species ℍ ω Γ))
    , (ν(M) C |ₛ parallel.from_list As)
    ≈ ((ν(M) C |ₛ parallel.from_list As') |ₛ parallel.from_list Bs)
    ∧ (∀ A ∈ As', normalise.atom normalise.kind'.atom A ∧ level.zero ∈ A)
    ∧ (∀ B ∈ Bs, normalise.atom normalise.kind'.atom B)
| Γ M [] C _ :=
  ⟨ [], [],
    calc  (ν(M) C |ₛ nil)
        ≈ (ν(M) (C |ₛ nil) |ₛ nil)
          : equiv.ξ_restriction M equiv.parallel_nil₂

    ... ≈ ((ν(M) C |ₛ nil) |ₛ nil) : begin
            suffices : (ν(M) (C |ₛ nil) |ₛ rename name.extend nil) ≈ ((ν(M) C |ₛ nil) |ₛ nil),
              simpa only [rename.nil],
            from equiv.ν_parallel' M
          end,
    λ x, false.elim,
    λ x, false.elim ⟩
| Γ M (A :: As) C atomAs :=
  let ⟨ As', Bs', eq, atomAs', atomBs' ⟩ := partition_restriction M As (C |ₛ A)
    (λ x mem, atomAs x (list.mem_cons_of_mem _ mem))
  in
  let eq' :=
    calc  (ν(M) C |ₛ parallel.from_list (A :: As))

          ≈ (ν(M) C |ₛ A |ₛ parallel.from_list As)
            : equiv.ξ_restriction M $ equiv.ξ_parallel₂ $ parallel.from_list_cons A As

      ... ≈ (ν(M) (C |ₛ A) |ₛ parallel.from_list As)
            : equiv.ξ_restriction M $ equiv.parallel_assoc₂

      ... ≈ ((ν(M) (C |ₛ A) |ₛ parallel.from_list As') |ₛ parallel.from_list Bs')
            : eq
  in

  if h : level.zero ∈ A then
    -- The restriction is used within this term - keep it in.
    ⟨ A :: As', Bs',
     calc  (ν(M) C |ₛ parallel.from_list (A :: As))
         ≈ ((ν(M) (C |ₛ A) |ₛ parallel.from_list As') |ₛ parallel.from_list Bs')
           : eq'

     ... ≈ ((ν(M) C |ₛ A |ₛ parallel.from_list As') |ₛ parallel.from_list Bs')
           : equiv.ξ_parallel₁ $ equiv.ξ_restriction M $ equiv.parallel_assoc₁

     ... ≈ ((ν(M) C |ₛ parallel.from_list (A :: As')) |ₛ parallel.from_list Bs')
           : equiv.ξ_parallel₁ $ equiv.ξ_restriction M
           $ equiv.ξ_parallel₂ (symm (parallel.from_list_cons A As')),
    λ x mem, begin
      clear partition_restriction _let_match,
      cases mem, case or.inr { from atomAs' x mem }, subst mem,
      from ⟨ atomAs x (list.mem_cons_self _ _), h ⟩,
    end,
    atomBs' ⟩
  else
    ⟨ As', drop h :: Bs',
      -- The restriction is not within this term - lift it out.
      calc  (ν(M) C |ₛ parallel.from_list (A :: As))
          ≈ ((ν(M) (C |ₛ A) |ₛ parallel.from_list As') |ₛ parallel.from_list Bs')
            : eq'

      ... ≈ ((ν(M) A |ₛ C |ₛ parallel.from_list As') |ₛ parallel.from_list Bs')
            : equiv.ξ_parallel₁ $ equiv.ξ_restriction M
            $ trans (equiv.ξ_parallel₁ equiv.parallel_symm) equiv.parallel_assoc₁

      ... ≈ (((ν(M) C |ₛ parallel.from_list As') |ₛ drop h) |ₛ parallel.from_list Bs')
            : equiv.ξ_parallel₁ begin
                suffices : (ν(M) rename name.extend (drop h) |ₛ C |ₛ parallel.from_list As')
                           ≈ (drop h |ₛ (ν(M) C |ₛ parallel.from_list As')),
                    rw drop_extend h at this, from trans this equiv.parallel_symm,
                from equiv.ν_parallel₁ M
              end

      ... ≈ ((ν(M) C |ₛ parallel.from_list As') |ₛ drop h |ₛ parallel.from_list Bs')
            : equiv.parallel_assoc₁

      ... ≈ ((ν(M) C |ₛ parallel.from_list As') |ₛ parallel.from_list (drop h :: Bs'))
            : equiv.ξ_parallel₂ (symm (parallel.from_list_cons (drop h) Bs')),
      atomAs',
      λ x mem, begin
        clear partition_restriction _let_match,
        cases mem, case or.inr { from atomBs' x mem }, subst mem,
        from normalise.drop_atom h (atomAs A (list.mem_cons_self _ _)),
      end ⟩

/-- Build a restriction from a list of parallel components, or drop it if it is
    empty. -/
def build_restriction {Γ} : ∀ (M : affinity ℍ)
    (As : list (species ℍ ω (context.extend M.arity Γ)))
    (Bs : list (species ℍ ω Γ))
  , (∀ A ∈ As, normalise.atom normalise.kind'.atom A ∧ level.zero ∈ A)
  → (∀ B ∈ Bs, normalise.atom normalise.kind'.atom B)
  → Σ' (Cs : list (species ℍ ω Γ))
    , parallel.from_list ((ν(M) parallel.from_list As) :: Bs)
    ≈ parallel.from_list Cs
    ∧ (∀ C ∈ Cs, normalise.atom normalise.kind'.atom C)
| M [] Bs atomAs atomBs :=
  ⟨ Bs,
    calc  parallel.from_list ((ν(M) nil) :: Bs)
        ≈ ((ν(M) nil) |ₛ parallel.from_list Bs) : parallel.from_list_cons _ Bs
    ... ≈ (nil |ₛ parallel.from_list Bs) : begin
            suffices : equiv (ν(M) rename name.extend nil) nil,
            { simp only [rename.nil] at this, from equiv.ξ_parallel₁ this },
            from equiv.ν_drop₁ M,
          end
    ... ≈ parallel.from_list Bs : equiv.parallel_nil',
    atomBs ⟩
| M (A::As) Bs atomAs atomBs :=
  ⟨ (ν(M) parallel.from_list (A::As)) :: Bs, equiv.rfl,
    λ x mem, begin
      cases mem,
      case or.inr { from atomBs x mem },
      subst mem,
      suffices : normalise.atom (normalise.kind'.in_nu M) (parallel.from_list (A :: As)),
      { from normalise.atom.restriction M this },


      induction As generalizing A,
      case list.nil {
        cases atomAs A (list.mem_cons_self A []) with atomA usesM,
        from normalise.atom.nu_one M atomA usesM,
      },
      case list.cons : A' As ih {
        cases atomAs A (list.mem_cons_self A _) with atomA usesM,
        from normalise.atom.nu_cons M atomA usesM (ih A' (λ x mem, atomAs x (list.mem_cons_of_mem _ mem))),
      }
    end ⟩

/-- Simplifies a restriction as much as possible. This lifts any parallel
    components out of it if possible, and removes the entire thing if possible. -/
def normalise_restriction {Γ} : ∀ (M : affinity ℍ)
    (As : list (species ℍ ω (context.extend (M.arity) Γ)))
  , (∀ A ∈ As, normalise.atom normalise.kind'.atom A)
  → Σ' (Bs : list (species ℍ ω Γ))
    , (ν(M) parallel.from_list As) ≈ parallel.from_list Bs
    ∧ ∀ B ∈ Bs, normalise.atom normalise.kind'.atom B
| M As atomAs :=
  let ⟨ As₁, Bs, eq, atomAs₁, atomBs ⟩ := partition_restriction M As nil atomAs in
  let ⟨ As₂, eq₂, atomAs₂ ⟩ := build_restriction M As₁ Bs atomAs₁ atomBs in
  ⟨ As₂,
    calc  (ν(M) parallel.from_list As)

        ≈ (ν(M) nil |ₛ parallel.from_list As)
          : equiv.ξ_restriction M (symm equiv.parallel_nil')

    ... ≈ ((ν(M) nil |ₛ parallel.from_list As₁) |ₛ parallel.from_list Bs) : eq

    ... ≈ ((ν(M) parallel.from_list As₁) |ₛ parallel.from_list Bs)
          : equiv.ξ_parallel₁ $ equiv.ξ_restriction M equiv.parallel_nil'

    ... ≈ parallel.from_list As₂
        : trans (symm (parallel.from_list_cons _ Bs)) eq₂,
  atomAs₂ ⟩

/-- Wraps species.equiv to work on both species and lists of choices. -/
@[nolint has_inhabited_instance]
def equivalence_of : ∀ {k} {Γ}, whole ℍ ω k Γ → Type
| kind.species Γ A :=
  Σ' (Bs : list (species ℍ ω Γ))
  , A ≈ parallel.from_list Bs
  ∧ ∀ B ∈ Bs, normalise.atom normalise.kind'.atom B
| kind.choices Γ A :=
  Σ' (B : choices ℍ ω Γ)
  , (Σ# A) ≈ (Σ# B)
  ∧ normalise.atom normalise.kind'.choices B

/-- Reduce a term to some equivalent normal form. -/
def normalise_to : ∀ {k} {Γ} (A : whole ℍ ω k Γ), equivalence_of A
| ._ ._ nil := ⟨ [], refl _, λ x, false.elim ⟩
| ._ ._ (apply D as) := ⟨ [apply D as], refl _, λ x mem, begin
    cases mem, case or.inr { cases mem }, subst mem,
    from normalise.atom.apply D as,
  end⟩
| ._ Γ (A |ₛ B) :=
  let ⟨ A', ea, atomA ⟩ := normalise_to A in
  let ⟨ B', eb, atomB ⟩ := normalise_to B in
  ⟨ A' ++ B',
    calc  (A |ₛ B)
        ≈ (parallel.from_list A' |ₛ parallel.from_list B')
          : trans (equiv.ξ_parallel₁ ea) (equiv.ξ_parallel₂ eb)
    ... ≈ parallel.from_list (A' ++ B') : symm (parallel.from_append A' B'),
    λ x mem, or.elim (list.mem_append.mp mem) (atomA x) (atomB x) ⟩
| ._ Γ (ν(M) A) :=
  let ⟨ A', ea, atomA ⟩ := normalise_to A in
  let ⟨ B, eb, atomB ⟩ := normalise_restriction M A' atomA in
  ⟨ B, trans (equiv.ξ_restriction M ea) eb, atomB ⟩
| ._ Γ (Σ# As) :=
  let ⟨ As', eqa, atom ⟩ := normalise_to As in
  ⟨ [ Σ# As' ], eqa, λ x mem, begin
    cases mem, case or.inr { cases mem }, subst mem,
    from normalise.atom.choice atom,
  end ⟩

| ._ Γ whole.empty := ⟨ whole.empty, refl _, normalise.atom.empty ⟩
| ._ Γ (whole.cons π A As) :=
  let ⟨ A', eqa, atomA ⟩ := normalise_to A in
  let ⟨ As', eqas, atomAs ⟩ := normalise_to As in
  ⟨ whole.cons π (parallel.from_list A') As',
    trans (equiv.ξ_choice_here π eqa) (equiv.ξ_choice_there π eqas),
    normalise.mk_choice π A' atomA atomAs ⟩

using_well_founded {
  rel_tac := λ _ _,
    `[exact ⟨_, measure_wf (λ x, whole.sizeof ℍ ω x.fst x.snd.fst x.snd.snd ) ⟩ ],
  dec_tac := tactic.fst_dec_tac,
}

/-- Reduce a term to some equivalent normal form. -/
def normalise : ∀ {k} {Γ}, whole ℍ ω k Γ → whole ℍ ω k Γ
| kind.species Γ A := parallel.from_list (normalise_to A).fst
| kind.choices Γ A := (normalise_to A).fst

namespace normalise
  /-- Two species are n-equivalent if they normalise to the same term. -/
  def equiv {Γ : context} (A B : species ℍ ω Γ) : Prop := normalise A = normalise B

  instance equiv.decide [decidable_eq ℍ] {Γ : context} : decidable_rel (@equiv ℍ ω Γ)
  | A B := species.whole.decidable_eq ℍ ω kind.species Γ (normalise A) (normalise B)

  lemma equiv.refl {Γ} : reflexive (@equiv ℍ ω Γ)
  | A := rfl

  lemma equiv.symm {Γ} : symmetric (@equiv ℍ ω Γ)
  | A B eql := eq.symm eql

  lemma equiv.trans {Γ} : transitive (@equiv ℍ ω Γ)
  | A B C ab bc := eq.trans ab bc

  /-- If two terms reduce to the same thing, then they are equivalent. -/
  lemma equiv.imp_congruent {Γ} {A B : species ℍ ω Γ} : equiv A B → A ≈ B
  | eq := begin
      unfold equiv normalise at eq,
      have : A ≈ parallel.from_list (normalise_to B).1 := eq ▸ (normalise_to A).2.1,
      from trans this (symm (normalise_to B).2.1),
  end

  lemma equiv.normalise_to {Γ} {A B : species ℍ ω Γ} :
    equiv A B → (normalise_to A).1 = (normalise_to B).1
  | ab := begin
    unfold equiv normalise at ab, clear equiv.normalise_to,
    rcases normalise_to A with ⟨ As, eq, atomA ⟩, assume ab, simp only [] at ⊢ ab, clear eq,
    rcases normalise_to B with ⟨ Bs, eq, atomB ⟩, assume ab, simp only [] at ⊢ ab, clear eq,

    from atom_parallel_inj As Bs ab atomA atomB,
  end

  /-- Equivalence under normalisation. Namely, two species are equivalent if they
      normalise to identical species. -/
  def setoid {Γ} : setoid (species ℍ ω Γ) :=
    ⟨ equiv, ⟨ @equiv.refl ℍ ω Γ, @equiv.symm ℍ ω Γ, @equiv.trans ℍ ω Γ ⟩ ⟩

  localized "attribute [instance] cpi.species.normalise.setoid" in normalise

  instance species'.has_repr [has_repr ℍ] {Γ} : has_repr (species' ℍ ω Γ)
    := ⟨ λ x, quot.lift_on x (λ x, repr (normalise x))
          (λ a b r, by { simp only [], from congr_arg repr r }) ⟩
end normalise

end species
end cpi

#lint-
