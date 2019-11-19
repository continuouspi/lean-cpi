import data.cpi.species.equivalence data.cpi.species.order
import data.list.sort

namespace cpi
namespace species

variables {ℍ : Type} {ω : context}

private def drop_var {Γ} {n}
    (P : level (context.extend n Γ) → Prop) (p : (¬ P level.zero))
  : Π a, P (name.to_level a) → name Γ
| (name.zero idx) q := by { unfold name.to_level at q, contradiction }
| (name.extend a) _ := a

private lemma drop_var_compose {Γ} {n}
  (P : level (context.extend n Γ) → Prop) (p : (¬ P level.zero))
  : (λ a f, name.extend (drop_var P p a f)) = λ a _, a
  := funext $ λ a, funext $ λ q, begin
    cases a,
    case name.zero { unfold name.to_level at q, contradiction },
    case name.extend { from rfl }
  end

private def drop {Γ} {n} {A : species ℍ ω (context.extend n Γ)}
  : level.zero ∉ A → species ℍ ω Γ
| free := rename_with A (drop_var (λ l, l ∈ A) free)

private lemma drop_extend {Γ} {n} {A : species ℍ ω (context.extend n Γ)} (fr : level.zero ∉ A)
  : rename name.extend (drop fr) = A
  := begin
    unfold drop,
    rw [rename_with_compose,
        drop_var_compose (λ l, l ∈ A) fr,
        rename_with_id]
  end

/-- Splits the parallel component of a restriction into two parts - those
    which can be lifted out of it, and those which cannot. -/
private def partition_restriction : ∀ {Γ}
    (M : affinity ℍ)
    (As : list (species ℍ ω (context.extend (M.arity) Γ)))
    (C : species ℍ ω (context.extend (M.arity) Γ))
  , Σ' (As' : list (species ℍ ω (context.extend (M.arity) Γ)))
       (Bs : list (species ℍ ω Γ))
    , (ν(M) C |ₛ parallel.from_list As)
    ≈ ((ν(M) C |ₛ parallel.from_list As') |ₛ parallel.from_list Bs)
| Γ M [] C :=
  ⟨ [], [],
    calc  (ν(M) C |ₛ nil)
        ≈ (ν(M) (C |ₛ nil) |ₛ nil)
          : equiv.ξ_restriction M equiv.parallel_nil₂

    ... ≈ ((ν(M) C |ₛ nil) |ₛ nil) : begin
            suffices : (ν(M) (C |ₛ nil) |ₛ rename name.extend nil) ≈ ((ν(M) C |ₛ nil) |ₛ nil),
              simpa only [rename.nil],
            from equiv.ν_parallel' M
          end ⟩
| Γ M (A :: As) C :=
  let ⟨ As', Bs', eq ⟩ := partition_restriction M As (C |ₛ A) in
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
           $ equiv.ξ_parallel₂ (symm (parallel.from_list_cons A As')) ⟩
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
            : equiv.ξ_parallel₂ (symm (parallel.from_list_cons (drop h) Bs')) ⟩

/-- Simplifies a restriction as much as possible. This lifts any parallel
    components out of it if possible, and removes the entire thing if possible. -/
private def normalise_restriction [decidable_linear_order ℍ] : ∀ {Γ}
    (M : affinity ℍ)
    (A : species ℍ ω (context.extend (M.arity) Γ))
  , Σ' (B : species ℍ ω Γ), (ν(M) A) ≈ B
| Γ M A :=
  if h : level.zero ∈ A then
    let ⟨ As, Bs, eq ⟩ := partition_restriction M (parallel.to_list A) nil in
    let As' : list _ := (ν(M) parallel.from_list As) :: Bs in
    ⟨ parallel.from_list (list.insertion_sort (≤) As'),
      calc  (ν(M) A)
          ≈ (ν(M) parallel.from_list (parallel.to_list A))
            : equiv.ξ_restriction M (symm (parallel.from_to A))

      ... ≈ (ν(M) nil |ₛ parallel.from_list (parallel.to_list A))
            : equiv.ξ_restriction M (symm equiv.parallel_nil')

      ... ≈ ((ν(M) nil |ₛ parallel.from_list As) |ₛ parallel.from_list Bs) : eq

      ... ≈ ((ν(M) parallel.from_list As) |ₛ parallel.from_list Bs)
            : equiv.ξ_parallel₁ $ equiv.ξ_restriction M equiv.parallel_nil'

      ... ≈ parallel.from_list As'
            : symm (parallel.from_list_cons _ Bs)

      ... ≈ parallel.from_list (list.insertion_sort has_le.le As')
           : symm (parallel.permute (list.perm_insertion_sort (≤) _)) ⟩
  else
    -- Unused, drop
    ⟨ drop h, begin
      suffices : (ν(M) rename name.extend (drop h)) ≈ drop h,
        rw drop_extend h at this, from this,
      from equiv.ν_drop₁ M
     end ⟩


def equivalence_of : ∀ {k} {Γ}, whole ℍ ω k Γ → Type
| kind.species Γ A := Σ' (B : species ℍ ω Γ), A ≈ B
| kind.choices Γ A := Σ' (B : choices ℍ ω Γ), (Σ# A) ≈ (Σ# B)

/-- Reduce a term to some equivalent normal form. -/
def normalise_to [decidable_linear_order ℍ] : ∀ {k} {Γ} (A : whole ℍ ω k Γ), equivalence_of A
| ._ ._ nil := ⟨ nil, refl _ ⟩
| ._ ._ (apply D as) := ⟨ apply D as, refl _ ⟩
| ._ Γ (A |ₛ B) :=
  let ⟨ A', ea ⟩ := normalise_to A in
  let ⟨ B', eb ⟩ := normalise_to B in
  let as := parallel.to_list A' ++ parallel.to_list B' in
  ⟨ parallel.from_list (list.insertion_sort (≤) as),
    calc  (A |ₛ B)
        ≈ (A' |ₛ B') : trans (equiv.ξ_parallel₁ ea) (equiv.ξ_parallel₂ eb)
    ... ≈ parallel.from_list as : symm (parallel.from_to_append A' B')
    ... ≈ parallel.from_list (list.insertion_sort has_le.le as)
          : parallel.permute (list.perm.symm (list.perm_insertion_sort (≤) _)) ⟩
| ._ Γ (ν(M) A) :=
  let ⟨ A', ea ⟩ := normalise_to A in
  let ⟨ B, eb ⟩ := normalise_restriction M A' in
  ⟨ B, trans (equiv.ξ_restriction M ea) eb ⟩
| ._ Γ (Σ# As) :=
  let ⟨ As', eqa ⟩ := normalise_to As in
  let as := choice.to_list As' in
  ⟨ Σ# (choice.from_list (list.insertion_sort choice.le as)),
    calc  (Σ# As)
        ≈ (Σ# As') : eqa
    ... ≈ (Σ# choice.from_list as) : by rw choice.from_to
    ... ≈ Σ# choice.from_list (list.insertion_sort choice.le as)
          : choice.permute (list.perm.symm (list.perm_insertion_sort choice.le _)) ⟩

| ._ Γ whole.empty := ⟨ whole.empty, refl _ ⟩
| ._ Γ (whole.cons π A As) :=
  let ⟨ A', eqa ⟩ := normalise_to A in
  let ⟨ As', eqas ⟩ := normalise_to As in
  ⟨ whole.cons π A' As',
    trans (equiv.ξ_choice_here π eqa) (equiv.ξ_choice_there π eqas) ⟩

using_well_founded {
  rel_tac := λ _ _,
    `[exact ⟨_, measure_wf (λ x, whole.sizeof ℍ ω x.fst x.snd.fst x.snd.snd ) ⟩ ],
  dec_tac := tactic.fst_dec_tac,
}

def drop_nu : ∀ {Γ}
    (M : affinity ℍ)
    (A : species ℍ ω (context.extend (M.arity) Γ))
  , Σ' (B : species ℍ ω Γ), (ν(M) A) ≈ B
| Γ M A :=
  let As := parallel.to_list A in
  if h : level.zero ∈ A then
    ⟨ ν(M) A, refl _ ⟩
  else
    ⟨ drop h, begin
      suffices : (ν(M) rename name.extend (drop h)) ≈ drop h,
        rw drop_extend h at this, from this,
      from equiv.ν_drop₁ M
     end ⟩

/-- Reduce a term to some equivalent normal form. -/
def normalise [decidable_linear_order ℍ] : ∀ {k} {Γ}, whole ℍ ω k Γ → whole ℍ ω k Γ
| kind.species Γ A := (normalise_to A).fst
| kind.choices Γ A := (normalise_to A).fst

/-- If two terms reduce to the same thing, then they are equivalent. -/
lemma normalise_to_equiv [decidable_linear_order ℍ] :
  ∀ {Γ} {A B : species ℍ ω Γ}
  , normalise A = normalise B → A ≈ B
| Γ A B eq := begin
    unfold normalise at eq,
    have : A ≈ (normalise_to B).fst := eq ▸ (normalise_to A).snd,
    from trans this (symm (normalise_to B).snd),
end

end species
end cpi

#lint
