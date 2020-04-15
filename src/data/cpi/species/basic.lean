import data.cpi.prefix_expr data.cpi.affinity
import tactic.custom_wf tactic.known_induct

instance vector.has_empty {α : Type} : has_emptyc (vector α 0) := { emptyc := vector.nil }

namespace cpi

namespace species

/-- As the doc-strinct of 'whole' says, species and their choices are bundled
    into one type. We index on this "kind", which says whether this constructor
    represents a species, or is part of a guarded choice. -/
@[nolint has_inhabited_instance]
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
@[derive decidable_eq, nolint has_inhabited_instance]
inductive whole (ℍ : Type) (ω : context) : kind → context → Type
/- Species -/
| nil {} {Γ} : whole kind.species Γ
| apply {} {Γ} {n} : reference n ω → vector (name Γ) n → whole kind.species Γ
| choice {Γ} : whole kind.choices Γ → whole kind.species Γ
| parallel {Γ} : whole kind.species Γ → whole kind.species Γ → whole kind.species Γ
| restriction {Γ} (M : affinity ℍ) :
    whole kind.species (context.extend M.arity Γ) → whole kind.species Γ
/- Elements in the sum -/
| empty {} {Γ} : whole kind.choices Γ
| cons {Γ} {f} (π : prefix_expr ℍ Γ f) :
    whole kind.species (f.apply Γ) → whole kind.choices Γ → whole kind.choices Γ

/-- An alias for species within the `whole' datatype. -/
@[reducible, nolint dup_namespace]
def species (ℍ : Type) (ω : context) := @whole ℍ ω kind.species

/-- An alias for choices within the `whole' datatype. -/
@[reducible]
def choices (ℍ : Type) (ω : context) := @whole ℍ ω kind.choices

variables {ℍ : Type} {ω : context}

export whole (nil apply choice parallel restriction)
open whole

reserve infixr ` |ₛ ` :50
infixr ` |ₛ ` := parallel

notation `ν(` M `) ` A := restriction M A

reserve prefix `Σ#`: 40
prefix `Σ# ` := choice

/-- Construct a singleton choice from a prefix and species. -/
def choices.mk_one' {Γ f} (π : prefix_expr ℍ Γ f) (A : species ℍ ω (f.apply Γ))
  := whole.cons π A whole.empty

/-- Construct a singleton sum from a prefix and species. -/
def choices.mk_one {Γ f} (π : prefix_expr ℍ Γ f) (A : species ℍ ω (f.apply Γ))
  := Σ# (choices.mk_one' π A)

reserve infixr ` ⬝' `:75

infixr ` ⬝ ` := choices.mk_one
infixr ` ⬝' ` := choices.mk_one'

/-- Convert a species to a string. Can use `repr` normally. -/
protected def to_string [has_repr ℍ] : ∀ {k Γ}, whole ℍ ω k Γ → string
| k ._ nil := "0"
| k ._ (apply D as) := repr D ++ "(" ++ repr as.val ++ ")"
| k ._ (Σ# (whole.cons π A' whole.empty)) := to_string (whole.cons π A' whole.empty)
| k ._ (Σ# As) := "Σ#[" ++ to_string As ++ "]"
| k ._ (A' |ₛ B') := "(" ++ to_string A' ++ " | " ++ to_string B' ++ ")"
| k ._ (ν(M) a) := "(ν ?)(" ++ to_string a ++ ")"
| k ._ whole.empty := "∅"
| k ._ (whole.cons π A' whole.empty) := repr π ++ "." ++ to_string A'
| k ._ (whole.cons π A' (whole.cons π' B' As)) := repr π ++ "." ++ to_string A' ++ " + " ++ to_string (whole.cons π' B' As)

instance [has_repr ℍ] {Γ} : has_repr (species ℍ ω Γ) := ⟨ species.to_string ⟩

section free
  /-- Determine if any variable with a given level occurs within this species. -/
  def free_in {Γ} {k} (l : level Γ) (A : whole ℍ ω k Γ) : Prop := begin
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

  instance {Γ} {k} : has_mem (level Γ) (whole ℍ ω k Γ) := ⟨ free_in ⟩

  private def free_in_decide {Γ} {k} (l : level Γ) (A : whole ℍ ω k Γ) : decidable (free_in l A) := begin
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

  instance free_in.decidable {Γ} {k} {l} {A: whole ℍ ω k Γ} : decidable (free_in l A)
    := free_in_decide l A
end free

section rename
  /-- Apply a renaming function to a species, with a witness of presence. -/
  def rename_with : ∀ {Γ Δ} {k} (A : whole ℍ ω k Γ)
    (ρ : Π (a : name Γ), name.to_level a ∈ A → name Δ), whole ℍ ω k Δ
  | Γ Δ ._ nil ρ := nil
  | Γ Δ ._ (@apply _ _ _ n D as) ρ :=
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
  def rename {Γ Δ} {k} (ρ : name Γ → name Δ) (A : whole ℍ ω k Γ) : whole ℍ ω k Δ
    := rename_with A (λ a _, ρ a)

  /-- Renaming with the identity function does nothing. -/
  lemma rename_with_id : ∀ {Γ} {k} (A : whole ℍ ω k Γ), rename_with A (λ x _, x) = A
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
  lemma rename_id {Γ} {k} (A : whole ℍ ω k Γ): rename id A = A := rename_with_id A

  /-- Renaming twice is the same as renaming with a composed function. -/
  lemma rename_with_compose :
    ∀ {Γ Δ η} {k}
      (A : whole ℍ ω k Γ)
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
  lemma rename_compose {Γ Δ η k} (ρ : name Γ → name Δ) (σ : name Δ → name η) (A : whole ℍ ω k Γ)
    : rename σ (rename ρ A) = rename (σ ∘ ρ) A
    := rename_with_compose A (λ x _, ρ x) σ

  lemma rename_ext {Γ Δ k} {ρ : name Γ → name Δ} {n : ℕ} (A : whole ℍ ω k Γ)
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
  lemma rename.nil : rename ρ (@nil ℍ ω Γ) = nil := by unfold rename rename_with

  @[simp]
  lemma rename.invoke {n} (D : reference n ω) (as : vector (name Γ) n)
    : rename ρ (apply D as) = @apply ℍ _ _ _ D (vector.map ρ as)
    := begin
      cases as with as p,
      unfold rename rename_with vector.map, simp,
      from list.map_witness_to_map _ as,
    end

  @[simp]
  lemma rename.parallel (A B : species ℍ ω Γ)
    : rename ρ (A |ₛ B) = (rename ρ A |ₛ rename ρ B)
    := by unfold rename rename_with

  @[simp]
  lemma rename.restriction (M : affinity ℍ) (A : species ℍ ω (context.extend M.arity Γ))
    : rename ρ (ν(M)A ) = ν(M) (rename (name.ext ρ) A)
    := begin
      unfold rename rename_with name.ext,
      rw ← name.ext_with_discard (λ l, l ∈ A) ρ,
      from rfl
    end

  @[simp]
  lemma rename.choice (As : choices ℍ ω Γ): rename ρ (Σ# As) = Σ# (rename ρ As) := begin
    unfold rename rename_with,
    have : (λ (a : name Γ) (free : name.to_level a ∈ Σ# As), ρ a)
         = (λ (a : name Γ) (free : name.to_level a ∈ As), ρ a)
        := (funext $ λ a, funext $ λ free, rfl),
    rw this,
  end

  @[simp]
  lemma rename.empty : rename ρ (@whole.empty ℍ ω Γ) = empty := by unfold rename rename_with

  @[simp]
  lemma rename.cons {f} (π : prefix_expr ℍ Γ f) (A : species ℍ ω (f.apply Γ)) (As : choices ℍ ω Γ)
    : rename ρ (cons π A As)
    = cons (prefix_expr.rename ρ π) (rename (prefix_expr.ext π ρ) A) (rename ρ As)
    := begin
      unfold rename rename_with prefix_expr.rename prefix_expr.ext,
      rw prefix_expr.ext_with_discard π (λ l, _) ρ
    end

  lemma rename.inj :
    ∀ {Γ Δ k} {ρ : name Γ → name Δ}
    , function.injective ρ → function.injective (@rename ℍ ω Γ Δ k ρ)
  | Γ Δ _ ρ inj nil B eq := begin
      cases B;
      simp only [rename.nil, rename.invoke, rename.parallel, rename.choice, rename.restriction] at eq;
      contradiction,
    end
  | Γ Δ _ ρ inj (apply D as) B eq := begin
      cases B;
      simp only [rename.nil, rename.invoke, rename.parallel, rename.choice, rename.restriction] at eq;
      try { contradiction },
      case apply : n D' as' {
        rcases eq with ⟨ ⟨ _ ⟩, ⟨ eqD ⟩, eqAs ⟩,

        -- Show the vector is equal
        rcases as with ⟨ as, asL ⟩, rcases as' with ⟨ as', asL' ⟩,
        have eqAs := eq_of_heq eqAs,
        simp only [vector.map, subtype.mk_eq_mk] at eqAs,
        cases (list.injective_map_iff.mpr inj eqAs),

        from rfl,
      },
    end
  | Γ Δ _ ρ inj (A |ₛ B) C eq := begin
      cases C;
      simp only [rename.nil, rename.invoke, rename.parallel, rename.choice, rename.restriction] at eq;
      try { contradiction },

      case whole.parallel {
        cases rename.inj inj eq.left,
        cases rename.inj inj eq.right,
        from rfl,
      },
    end
  | Γ Δ _ ρ inj (Σ# As) B eq := begin
      cases B;
      simp only [rename.nil, rename.invoke, rename.parallel, rename.choice, rename.restriction] at eq;
      try { contradiction },
      case choice {
        cases rename.inj inj eq, from rfl,
      },
    end
  | Γ Δ _ ρ inj (ν(M) A) B eq := begin
      cases B;
      simp only [rename.nil, rename.invoke, rename.parallel, rename.choice, rename.restriction] at eq;
      try { contradiction },
      case restriction {
        rcases eq with ⟨ ⟨ _ ⟩, eqB ⟩,
        cases (rename.inj (name.ext.inj inj) (eq_of_heq eqB)),
        from rfl,
      }
    end

  | Γ Δ _ ρ inj whole.empty B eq := begin
      cases B;
      simp only [rename.empty, rename.cons] at eq;
      contradiction,
    end
  | Γ Δ _ ρ inj (whole.cons π A As) B eq := begin
      cases B;
      simp only [rename.empty, rename.cons] at eq;
      try { contradiction },
      case whole.cons : f π₂ B Bs {
        rcases eq with ⟨ ⟨ _ ⟩, eqπ, eqA, eqAs ⟩,
        cases prefix_expr.rename.inj inj (eq_of_heq eqπ),
        cases rename.inj inj eqAs,
        cases (rename.inj (prefix_expr.ext.inj π inj) (eq_of_heq eqA)),
        from rfl,
      }
    end


end rename_equations

/- Show parallel can be converted to/from a list (though not isomorphic). -/
namespace parallel
  /-- Unfold a parallel composition, turning it into a list of non-nil species. -/
  def to_list {Γ} : species ℍ ω Γ → list (species ℍ ω Γ)
  | nil := []
  | (A |ₛ B) := to_list A ++ to_list B
  | A := [A]

  /-- Re-fold a list of species, turning it back into a parallel composition. -/
  def from_list {Γ} : list (species ℍ ω Γ) → species ℍ ω Γ
  | [] := nil
  | [A] := A
  | (A :: As) := A |ₛ (from_list As)

  instance lift_to {Γ} : has_lift (species ℍ ω Γ) (list (species ℍ ω Γ)) := ⟨ to_list ⟩
  instance lift_from {Γ} : has_lift (list (species ℍ ω Γ)) (species ℍ ω Γ) := ⟨ from_list ⟩

  @[simp]
  lemma rename_from_list {Γ Δ} (ρ : name Γ → name Δ) :
    ∀ (As : list (species ℍ ω Γ))
    , rename ρ (from_list As) = from_list (list.map (rename ρ) As)
  | [] := rename.nil
  | [M] := rfl
  | (M :: M' :: Ms) := begin
    simp only [from_list, rename.parallel, list.map],
    from ⟨ rfl, rename_from_list (M' :: Ms) ⟩
  end

  /-- to_list should contian no non-nil elements. -/
  lemma to_list_nonnil {Γ}: ∀ (A : species ℍ ω Γ), nil ∉ to_list A
  | A := begin
    known_induction whole @whole.rec_on ℍ ω
      (λ k c A, begin
        cases k,
        case kind.species { from nil ∉ to_list A },
        case kind.choices { from true },
      end) kind.species Γ A,

    case nil : Γ mem { unfold to_list at mem, from list.not_mem_nil nil mem },
    case parallel : Γ A B iha ihb mem {
      unfold to_list at mem,
      from or.elim (list.mem_append.mp mem) iha ihb,
    },

    -- All remaining species and choices.
    repeat {
      intros, simp only [to_list, has_mem.mem, list.mem],
      assume mem, cases mem; contradiction
    },
    repeat { intros, from true.intro },
  end

  /-- to_list should contian no parallel elements. -/
  lemma to_list_nonparallel : ∀ {Γ} (A B₁ B₂  : species ℍ ω Γ), (B₁ |ₛ B₂) ∉ to_list A
  | Γ nil B₁ B₂ mem := by { unfold to_list at mem, cases mem }
  | Γ (A |ₛ B) B₁ B₂ mem := begin
    unfold to_list at mem,
    cases list.mem_append.mp mem;
    from to_list_nonparallel _ B₁ B₂ h,
  end
  | Γ (apply D as) B₁ B₂ mem := begin
    unfold to_list at mem, cases mem,
    contradiction, from mem,
  end
  | Γ (Σ# As) B₁ B₂ mem := begin
    unfold to_list at mem, cases mem,
    contradiction, from mem,
  end
  | Γ (ν(M) A) B₁ B₂ mem := begin
    unfold to_list at mem, cases mem,
    contradiction, from mem,
  end
end parallel

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

/-- A quotient of all structurally congruent species. -/
@[nolint has_inhabited_instance]
def species' (ℍ : Type) (ω Γ : context) [r : setoid (species ℍ ω Γ)] := quotient r

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

#lint-
