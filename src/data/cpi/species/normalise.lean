import data.cpi.species.equivalence data.cpi.species.order
import data.list.sort

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi
namespace species

variable {ω : context}

def drop_var {Γ} {n}
    (P : level (context.extend n Γ) → Prop) (p : (¬ P level.zero))
  : Π a, P (name.to_level a) → name Γ
| (name.zero idx) q := by { unfold name.to_level at q, contradiction }
| (name.extend a) _ := a

lemma drop_var_compose {Γ} {n}
  (P : level (context.extend n Γ) → Prop) (p : (¬ P level.zero))
  : (λ a f, name.extend (drop_var P p a f)) = λ a _, a
  := funext $ λ a, funext $ λ q, begin
    cases a,
    case name.zero { unfold name.to_level at q, contradiction },
    case name.extend { from rfl }
  end

def drop {Γ} {n} {A : species ω (context.extend n Γ)}
  : level.zero ∉ A → species ω Γ
| free := rename_with A (drop_var (λ l, l ∈ A) free)

lemma drop_extend {Γ} {n} {A : species ω (context.extend n Γ)} (fr : level.zero ∉ A)
  : rename name.extend (drop fr) = A
  := begin
    unfold drop,
    rw [rename_with_compose,
        drop_var_compose (λ l, l ∈ A) fr,
        rename_with_id]
  end

def drop_nu : ∀ {Γ} (A : species ω Γ), Σ' (B : species ω Γ), A ≈ B
| Γ (ν(M) A) :=
  if h : level.zero ∈ A then
    ⟨ ν(M) A, refl _ ⟩
  else
    ⟨ drop h, begin
      suffices : (ν(M) rename name.extend (drop h)) ≈ drop h,
        rw drop_extend h at this, from this,
      from equiv.ν_drop M
     end ⟩
| Γ x := ⟨ x, refl _ ⟩

def equivalence_of : ∀ {k} {Γ}, whole ω k Γ → Type
| kind.species Γ A := Σ' (B : species ω Γ), A ≈ B
| kind.choices Γ A := Σ' (B : choices ω Γ), (Σ# A) ≈ (Σ# B)

/-- Reduce a term to some equivalent normal form. -/
noncomputable def normalise_to : ∀ {k} {Γ} (A : whole ω k Γ), equivalence_of A
| ._ ._ nil := ⟨ nil, refl _ ⟩
| ._ ._ (apply D as) := ⟨ apply D as, refl _ ⟩
| ._ Γ (A |ₛ B) :=
  let ⟨ A', ea ⟩ := normalise_to A in
  let ⟨ B', eb ⟩ := normalise_to B in
  let as := parallel.to_list A' ++ parallel.to_list B' in
  ⟨ parallel.from_list (list.insertion_sort (≤) as),
    calc  (A |ₛ B)
        ≈ (A' |ₛ B') : trans (equiv.ξ_parallel₁ ea) (equiv.ξ_parallel₂ eb)
    ... ≈ parallel.from_list as : symm (parallel.from_to_append₂ A' B')
    ... ≈ parallel.from_list (list.insertion_sort has_le.le as)
          : parallel.permute (list.perm.symm (list.perm_insertion_sort (≤) _)) ⟩
| ._ Γ (ν(M) A) :=
  let ⟨ A', ea ⟩ := normalise_to A in
  if h : level.zero ∈ A then
    -- TODO: Shift some things out of the restriction when possible.
    ⟨ ν(M) A, refl _ ⟩
  else
    ⟨ drop h, begin
      suffices : (ν(M) rename name.extend (drop h)) ≈ drop h,
        simpa only [drop_extend],
      from equiv.ν_drop M
     end ⟩
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
    `[exact ⟨_, measure_wf (λ x, whole.sizeof ω x.fst x.snd.fst x.snd.snd ) ⟩ ],
  dec_tac := tactic.fst_dec_tac,
}

/-- Reduce a term to some equivalent normal form. -/
noncomputable def normalise : ∀ {k} {Γ}, whole ω k Γ → whole ω k Γ
| kind.species Γ A := (normalise_to A).fst
| kind.choices Γ A := (normalise_to A).fst

/-- If two terms reduce to the same thing, then they are equivalent. -/
lemma normalise_to_equiv :
  ∀ {Γ} {A B : species ω Γ}
  , normalise A = normalise B → A ≈ B
| Γ A B eq := begin
    unfold normalise at eq,
    have : A ≈ (normalise_to B).fst := eq ▸ (normalise_to A).snd,
    from trans this (symm (normalise_to B).snd),
end

end species
end cpi

#sanity_check
