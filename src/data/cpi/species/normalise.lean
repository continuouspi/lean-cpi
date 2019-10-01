import data.cpi.species.equivalence
import data.cpi.species.order

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

/-- Reduce a term to some equivalent normal form. -/
constant normalise_to : ∀ {Γ} (A : species ω Γ), Σ' (B : species ω Γ), A ≈ B

/-- Reduce a term to some equivalent normal form. -/
noncomputable def normalise {Γ} : species ω Γ → species ω Γ := λ A, (normalise_to A).fst

/-- If two terms reduce to the same thing, then they are equivalent. -/
lemma normalise_to_equiv :
  ∀ {Γ} {A B : species ω Γ}
  , normalise A = normalise B → A ≈ B
| Γ A B eq := begin
    unfold normalise at eq,
    have : A ≈ (normalise_to B).fst := eq ▸ (normalise_to A).snd,
    from trans this (symm (normalise_to B).snd),
end

/-- If two terms are equivalent, they reduce to the same thing. -/
axiom normalise_of_equiv :
  ∀ {Γ} {A B : species ω Γ}
  , A ≈ B → normalise A = normalise B

/-- Reducing again does nothing extra. -/
lemma normalise_normalise {Γ} (A : species ω Γ)
  : normalise (normalise A) = normalise A
  := normalise_of_equiv (symm (normalise_to A).snd)

/-- Equality of reduction is isomorphic to equivalence. -/
lemma normalise_equiv {Γ} (A B : species ω Γ)
  : (normalise A = normalise B) ↔ (A ≈ B)
  := ⟨ normalise_to_equiv, normalise_of_equiv ⟩

/-- Equality of reduction is isomorphic to equivalence (equality version). -/
lemma normalise_equiv_eq {Γ} (A B : species ω Γ)
  : (normalise A = normalise B) = (A ≈ B)
  := propext (normalise_equiv A B) -- Fun facts: propositional extensionality is an axiom.

/-- Decision procedure for equivalency of species.

    The fact that this is derivable from normalisation is obvious, but still
    pretty neat. -/
noncomputable instance equiv.decide {Γ}
  : @decidable_rel (species ω Γ) (≈)
  := λ A B,
    let h : decidable (normalise A = normalise B) := by apply_instance in
    decidable_of_decidable_of_iff h (normalise_equiv A B)

end species
end cpi

#sanity_check
