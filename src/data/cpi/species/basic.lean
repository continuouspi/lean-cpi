import data.cpi.prefix_expr
import data.cpi.affinity
import tactic.custom_wf

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi

namespace species

inductive kind
| species
| choices

/-- The set of species and choices.

    Species are composed of:
      - The inactive species
      - Invocation of a species definition
      - Guarded choice
      - Parallel composition
      - Local name declaration/restriction

    Choices are just a series of prefixes and a species to be evaluated after
    that prefix.

    While this could (and probably should) be defined as a mutually recursive
    datatype (or even a nested one, instead of a home-grown list), Lean's
    handling of recursive types is a little lacklustre: one cannot use the
    induction tactic, Lean often fails to show termination on its own, etc...

    In order to avoid these problems, we represent mutually-recursive type the
    same way that Lean does (as a single type indexed by what group it belongs
    to), but avoid the indirection that such a definition would introduce. -/
inductive whole (ω : context) : kind → context → Type
/- Species -/
| nil {} {Γ} : whole kind.species Γ
| apply {Γ} {n} : reference n ω → vector (name Γ) n → whole kind.species Γ
| choice {Γ} : whole kind.choices Γ → whole kind.species Γ
| parallel {Γ} : whole kind.species Γ → whole kind.species Γ → whole kind.species Γ
| restriction {Γ} (M : affinity) :
    whole kind.species (context.extend M.arity Γ) → whole kind.species Γ
/- Elements in the sum -/
| empty {} {Γ} : whole kind.choices Γ
| cons {Γ} {f} (π : prefix_expr Γ f) :
    whole kind.species (f Γ) → whole kind.choices Γ → whole kind.choices Γ


/-- An alias for species within the `whole' datatype. -/
@[reducible]
def species (ω : context) := @whole ω kind.species

/-- An alias for choices within the `whole' datatype. -/
@[reducible]
def choices (ω : context) := @whole ω kind.choices

variable {ω : context}

export whole (nil apply choice parallel restriction)
open whole

reserve infixr ` |ₛ ` :50
infixr ` |ₛ ` := parallel

notation `ν(` M `) ` A := restriction M A

reserve prefix `Σ#`: 40
prefix `Σ# ` := choice

section free
  def free_in {Γ} {k} (l : level Γ) (A : whole ω k Γ) : Prop := begin
    induction A,
    case nil { from false },
    case apply : Γ n D as { from ∃ a ∈ as.val, l ∈ a },
    case choice : Γ As ih { from ih l },
    case parallel : Γ A B ih_a ih_b { from ih_a l ∨ ih_b l },
    case restriction : Γ M A ih { from ih (level.extend l) },
    case whole.empty : Γ { from false },
    case whole.cons : Γ f π A As ih_a ih_as {
      from l ∈ π ∨ ih_a (prefix_expr.raise π l) ∨ ih_as l
    }
  end

  instance {Γ} {k} : has_mem (level Γ) (whole ω k Γ) := ⟨ free_in ⟩

  private def free_in_decide {Γ} {k} (l : level Γ) (A : whole ω k Γ) : decidable (free_in l A) := begin
    induction A,

    case nil { from decidable.false },
    case apply : { unfold free_in, apply_instance },
    case choice : Γ As ih { from ih l },
    case parallel : Γ A B ih_a ih_b { from @or.decidable _ _ (ih_a l) (ih_b l) },
    case restriction : Γ M A ih { from ih (level.extend l) },
    case whole.empty { from decidable.false },
    case whole.cons : Γ f π A As ih_a ih_as {
      from @or.decidable (l ∈ π) _ _
        (@or.decidable _ _ (ih_a (prefix_expr.raise π l)) (ih_as l))
    }
  end

  instance free_in.decidable {Γ} {k} {l} {A: whole ω k Γ} : decidable (free_in l A)
    := free_in_decide l A
end free

section rename
  /-- Apply a renaming function to a species, with a witness of presence. -/
  def rename_with : ∀ {Γ Δ} {k} (A : whole ω k Γ)
    (ρ : Π (a : name Γ), name.to_level a ∈ A → name Δ), whole ω k Δ
  | Γ Δ ._ nil ρ := nil
  | Γ Δ ._ (@apply _ _ n D as) ρ :=
    let as' := list.map_witness as.val (λ x mem, ρ x ⟨ x, mem, name.to_level_at x ⟩) in
    let eq : list.length as' = n := by { rw (list.map_witness_length as.val _), from as.property } in
    apply D ⟨ as', eq ⟩
  | Γ Δ ._ (A |ₛ B) ρ :=
    rename_with A (λ a free, ρ a (or.inl free)) |ₛ
    rename_with B (λ a free, ρ a (or.inr free))
  | Γ Δ ._ (ν(M)A) ρ :=
      let ρ' := λ a free, ρ a (free) in
      ν(M) rename_with A (name.ext_with (λ l, l ∈ A) ρ')
  | Γ Δ ._ (Σ# As) ρ:=
    let ρ' := (λ a free, ρ a (free)) in
    Σ# rename_with As ρ'
  | Γ Δ ._ empty ρ := empty
  | Γ Δ ._ (cons π A As) ρ :=
    cons
      (prefix_expr.rename_with π (λ a free, ρ a (or.inl free)))
      (rename_with A
        (prefix_expr.ext_with π (λ l, l ∈ A) (λ a free, ρ a (or.inr (or.inl free)))))
      (rename_with As (λ a free, ρ a (or.inr (or.inr free))))
  using_well_founded {
    rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ s, sizeof s.snd.snd.snd.fst)⟩],
    dec_tac := tactic.fst_dec_tac,
  }

  /-- A simpler version of rename_with, which does not require a witness. -/
  @[reducible]
  def rename {Γ Δ} {k} (ρ : name Γ → name Δ) (A : whole ω k Γ) : whole ω k Δ
    := rename_with A (λ a _, ρ a)

  /-- Renaming with the identity function does nothing. -/
  lemma rename_with_id : ∀ {Γ} {k} (A : whole ω k Γ), rename_with A (λ x _, x) = A
  | Γ ._ nil := by unfold rename_with
  | Γ ._ (apply D as) := by simp [rename_with]
  | Γ ._ (A |ₛ B) :=
    let a : rename_with A _ = A := rename_with_id A in
    let b : rename_with B _ = B := rename_with_id B in
    by { unfold rename_with, rw [a, b] }
  | Γ ._ ν(M)A :=
    let a : rename_with A _ = A := rename_with_id A in
    begin
        simp only [rename_with],
        have h := name.ext_with_id (λ l, l ∈ A),
        have g
          : (λ (x : name Γ) (free : (λ (l : level (context.extend (M.arity) Γ)), l ∈ A) (level.extend (name.to_level x))), x)
          = (λ (a : name Γ) (free : name.to_level a ∈ ν(M) A), a) := rfl,
        rw g at h, rw h,
        simp [a]
    end
  | Γ ._ (Σ# As) := by { simp only [rename_with], from rename_with_id As }
  | Γ ._ empty := by unfold rename_with
  | Γ ._ (cons π A As) :=
    let π' : prefix_expr.rename_with π _ = π := prefix_expr.rename_with_id π in
    let a : rename_with A _ = A := rename_with_id A in
    let as : rename_with As _ = As := rename_with_id As in
    begin
      simp [rename_with],
      rw prefix_expr.ext_with_id,
      simp [π', a, as]
    end

  /-- Renaming with the identity function is the identity. -/
  lemma rename_id {Γ} {k} (A : whole ω k Γ) : rename id A = A := rename_with_id A

  /-- Renaming twice is the same as renaming with a composed function. -/
  lemma rename_with_compose :
    ∀ {Γ Δ η} {k}
      (A : whole ω k Γ)
      (ρ : (Π (a : name Γ), name.to_level a ∈ A → name Δ))
      (σ : name Δ → name η)
    , rename σ (rename_with A ρ) = rename_with A (λ x f, σ (ρ x f))
  | Γ Δ η ._ nil ρ σ := by unfold rename rename_with
  | Γ Δ η ._ (apply D as) ρ σ := by simp [rename, rename_with, list.map_witness_to_map]
  | Γ Δ η ._ (A |ₛ B) ρ σ :=
    let a := rename_with_compose A (λ a free, ρ a (or.inl free)) σ in
    let b := rename_with_compose B (λ a free, ρ a (or.inr free)) σ in
    by { simp [rename, rename_with], from and.intro a b }
  | Γ Δ η ._ (ν(M) A) ρ σ := begin
      simp [rename, rename_with, name.ext_with],

      suffices
        : rename (name.ext σ) (rename_with A (name.ext_with (λ l, l ∈ A) ρ))
        = rename_with A (name.ext_with (λ l, l ∈ A) (λ a free, σ (ρ a free))),
        unfold rename name.ext at this,
        rw ← name.ext_with_discard (λ l, l ∈ rename_with A (name.ext_with (λ l, l ∈ A) ρ)) σ at this,
        from this,

      have h := rename_with_compose A
            (name.ext_with (λ l, l ∈ A) (λ a free, ρ a (free)))
            (name.ext σ),

      from name.ext_with_comp (λ l, l ∈ A) ρ σ ▸ h,
    end
  | Γ Δ η ._ (Σ# As) ρ σ := begin
      simp [rename, rename_with],
      from rename_with_compose As _ σ
    end
  | Γ Δ η ._ empty ρ σ := by unfold rename rename_with
  | Γ Δ η ._ (cons π A As) ρ σ := begin
      simp [rename, rename_with, prefix_expr.ext_with],

      have π' := prefix_expr.rename_with_compose π (λ a f, ρ a (or.inl f)) σ,
      have A' := rename_with_compose A
        (prefix_expr.ext_with π (λ l, l ∈ A) (λ a f, ρ a (or.inr (or.inl f))))
        (prefix_expr.ext π σ),
      have As' := rename_with_compose As (λ a f, ρ a (or.inr (or.inr f))) σ,

      -- Massage A and ⊢ into shape
      rw prefix_expr.ext_with_comp π (λ l, l ∈ A) at A',
      unfold rename prefix_expr.ext at A',

      rw prefix_expr.ext_with_discard
        (prefix_expr.rename_with π (λ a free, ρ a _))
        (λ l, l ∈ rename_with A (prefix_expr.ext_with π (λ l, l ∈ A) (λ a free, ρ a _)))
        σ,
      rw prefix_expr.rename_with_ext_with π,

      from ⟨ π', A', As' ⟩,
    end

  /-- Renaming twice is the same as renaming with a composed function. -/
  lemma rename_compose {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η) (A : species ω Γ)
    : rename σ (rename ρ A) = rename (σ ∘ ρ) A
    := rename_with_compose A (λ x _, ρ x) σ

  lemma rename_ext {Γ Δ} {ρ : name Γ → name Δ} {n : ℕ} (A : species ω Γ)
    : rename name.extend (rename ρ A)
    = rename (name.ext ρ) (rename (@name.extend _ n) A)
    := by rw [rename_compose, ← name.ext_extend, rename_compose]
end rename

/- Various equational lemmas for rewrite.

   This just simplifies the work needed to do when using simple rewriting
   functions (such as in equivalency or pseduo-application).-/
section rename_equations
  variables {Γ Δ : context} {ρ : name Γ → name Δ}

  @[simp]
  lemma rename.nil : rename ρ (@nil ω Γ) = nil := by unfold rename rename_with

  @[simp]
  lemma rename.parallel (A B : species ω Γ)
    : rename ρ (A |ₛ B) = (rename ρ A |ₛ rename ρ B)
    := by unfold rename rename_with

  @[simp]
  lemma rename.restriction (M : affinity) (A : species ω (context.extend M.arity Γ))
    : rename ρ (ν(M)A ) = ν(M) (rename (name.ext ρ) A)
    := begin
      unfold rename rename_with name.ext,
      rw ← name.ext_with_discard (λ l, l ∈ A) ρ,
      from rfl
    end

  @[simp]
  lemma rename.choice (As : choices ω Γ): rename ρ (Σ# As) = Σ# (rename ρ As) := begin
    unfold rename rename_with,
    have : (λ (a : name Γ) (free : name.to_level a ∈ Σ# As), ρ a)
         = (λ (a : name Γ) (free : name.to_level a ∈ As), ρ a)
        := (funext $ λ a, funext $ λ free, rfl),
    rw this,
  end

  @[simp]
  lemma rename.empty : rename ρ (@whole.empty ω Γ) = empty := by unfold rename rename_with

  @[simp]
  lemma rename.sum {f} (π : prefix_expr Γ f) (A : species ω (f Γ)) (As : choices ω Γ)
    : rename ρ (cons π A As)
    = cons (prefix_expr.rename ρ π) (rename (prefix_expr.ext π ρ) A) (rename ρ As)
    := begin
      unfold rename rename_with prefix_expr.rename prefix_expr.ext,
      rw prefix_expr.ext_with_discard π (λ l, _) ρ
    end

end rename_equations

/- Show parallel can be converted to/from a list (though not isomorphic). -/
namespace parallel
  def to_list {Γ} : species ω Γ → list (species ω Γ)
  | nil := []
  | (A |ₛ B) := to_list A ++ to_list B
  | A := [A]

  def from_list {Γ} : list (species ω Γ) → species ω Γ
  | [] := nil
  | [A] := A
  | (A :: As) := A |ₛ (from_list As)

  instance lift_to {Γ} : has_lift (species ω Γ) (list (species ω Γ)) := ⟨ to_list ⟩
  instance lift_from {Γ} : has_lift (list (species ω Γ)) (species ω Γ) := ⟨ from_list ⟩
end parallel

/- Show choice can be converted to/from a list and is isomorphic. -/
namespace choice
  def to_list {Γ} : choices ω Γ → list (Σ' {f} (π : prefix_expr Γ f), species ω (f Γ))
  | empty := []
  | (cons π A As) := ⟨ _, π, A ⟩ :: to_list As

  def from_list {Γ} : list (Σ' {f} (π : prefix_expr Γ f), species ω (f Γ)) → choices ω Γ
  | [] := empty
  | (⟨ _, π, A ⟩ :: As) := cons π A (from_list As)

  instance lift_to {Γ} : has_lift (choices ω Γ) (list (Σ' {f} (π : prefix_expr Γ f), species ω (f Γ)))
    := ⟨ to_list ⟩
  instance lift_from {Γ} : has_lift (list (Σ' {f} (π : prefix_expr Γ f), species ω (f Γ))) (choices ω Γ)
    := ⟨ from_list ⟩

  lemma from_to {Γ} : ∀ (A : choices ω Γ), from_list (to_list A) = A
  | empty := by unfold to_list from_list
  | (cons π A As) := by { simp [to_list, from_list], from from_to As }

  lemma to_from {Γ} :
    ∀ (As : list (Σ' {f} (π : prefix_expr Γ f), species ω (f Γ)))
    , to_list (from_list As) = As
  | [] := by unfold to_list from_list
  | (⟨ _, π,  A⟩ :: As) := by { simp [to_list, from_list], from to_from As }
end choice

end species

/- Re-export all the definitions. Don't ask - apparently export within
   namespaces is a little broken. -/
export species (renaming
  whole.nil → species.nil
  whole.apply → species.apply
  whole.parallel → species.parallel
  whole.restriction → species.restriction
  whole.choice → species.choice
  species → species
)

end cpi

/- Re-export all the definitions. Don't ask - apparently export within
   namespaces is a little broken. -/
export cpi.species (renaming
  whole.nil → cpi.species.nil
  whole.apply → cpi.species.apply
  whole.parallel → cpi.species.parallel
  whole.restriction → cpi.species.restriction
  whole.choice → cpi.species.choice
  species → cpi.species
)


#sanity_check
