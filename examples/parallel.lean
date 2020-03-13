import data.cpi.semantics.basic
-- import data.cpi.semantics.with_exact
import data.cpi.semantics.with_normalise

open cpi
open cpi.species

open_locale normalise

def aff : affinity ℚ :=
  { arity := 2,
    f := λ x y,
      if h : (x = 0 ∧ y = 1) ∨ (y = 0 ∧ x = 1) then
        some (1/3)
      else
        none,
    symm := λ x y, begin
      by_cases x = 0 ∧ y = 1 ∨ y = 0 ∧ x = 1,
      simp only [dif_pos h, dif_pos (or.swap h)],
      simp only [dif_neg h, dif_neg (h ∘ or.swap)],
    end }


def ω : context := context.nil
def Γ : context := context.extend aff.arity context.nil
def ℓ : lookup ℚ ω Γ
| n r := by cases r

def a : name Γ := name.zero ⟨ 0, nat.succ_pos 1 ⟩
def b : name Γ := name.zero ⟨ 1, lt_add_one 1 ⟩

@[pattern] def A : species ℚ ω Γ := a # ⬝ nil
@[pattern] def B : species ℚ ω Γ := b # ⬝ nil
@[pattern] def AB : species ℚ ω Γ := A |ₛ B

def A.transitions : fintype (transition.transition_from ℓ A) := transition.enumerate_choices ℓ _
def B.transitions : fintype (transition.transition_from ℓ B) := transition.enumerate_choices ℓ _

def AB.transition_set : finset (transition.transition_from ℓ AB) :=
finset.insert_nmem'
  ⟨ _, #a, _, transition.parL_concretion B (transition.choice₁ a list.nil rfl 0 _ _) ⟩
  (finset.insert_nmem'
    ⟨ _, #b, _, transition.parR_concretion A (transition.choice₁ b list.nil rfl 0 _ _) ⟩
    (finset.singleton ⟨ _, τ⟨ a, b ⟩, _,
      transition.com₁
      (transition.choice₁ a list.nil rfl 0 _ _)
      (transition.choice₁ b list.nil rfl 0 _ _) ⟩)
    (finset.not_mem_singleton.mpr (λ x, by cases x))
  ) (λ mem, begin
    simp only [finset.insert_nmem', finset.insert_nmem, finset.mem_def] at mem,
    cases multiset.mem_cons.mp mem,
    case or.inl { cases h },
    cases finset.mem_singleton.mp h,
  end)

def AB.transitions : fintype (transition.transition_from ℓ AB) :=
  { elems := AB.transition_set,
    complete := λ ⟨ k, α, E, t ⟩, begin
      cases t,
      case transition.parL_species : α E t { cases t, cases t_a },
      case transition.parR_species : α E t { cases t, cases t_a },

      case transition.parL_concretion : α b y E t {
        cases t,
        case transition.ξ_choice : t { cases t },
        subst t_b_len,

        simp only [AB.transition_set, finset.insert_nmem', finset.insert_nmem, finset.mem_def],
        from multiset.mem_cons_self _ _,
      },

      case transition.parR_concretion : α b y E t {
        cases t,
        case transition.ξ_choice : t { cases t },
        subst t_b_len,

        simp only [AB.transition_set, finset.insert_nmem', finset.insert_nmem, finset.mem_def],
        from multiset.mem_cons_of_mem (multiset.mem_cons_self _ _),
      },

      case transition.com₁ : x y a b F G tf tg {
        simp only [AB.transition_set, finset.insert_nmem', finset.insert_nmem, finset.mem_def],
        refine multiset.mem_cons_of_mem (multiset.mem_cons_of_mem (finset.mem_singleton.mpr _)),

        cases tf, case transition.ξ_choice : t { cases t }, subst tf_b_len,
        cases tg, case transition.ξ_choice : t { cases t }, cases tg_b_len,
        from rfl,
      },

    end }

def conc := function.embedding.refl ℚ

/-- ∂(c•(A|B)) -/
def potential_species : interaction_space ℚ ℚ ω Γ
  := finset.sum AB.transitions.elems potential_interaction_space

/-- d(c•(A|B))/dt -/
def immediate_species : process_space ℚ ℚ ω Γ
  := finset.sum AB.transitions.elems (immediate_process_space conc)
   + (½ : ℚ) • (potential_species ⊘[conc] potential_species)

#eval immediate_species

/- -------------------------------------------- -/

/-- ∂(c•A) -/
def potential_A : interaction_space ℚ ℚ ω Γ
  := finset.sum A.transitions.elems potential_interaction_space

/-- ∂(c•B) -/
def potential_B : interaction_space ℚ ℚ ω Γ
  := finset.sum B.transitions.elems potential_interaction_space

/-- ∂(c•A || c•B) -/
def potential_proc : interaction_space ℚ ℚ ω Γ := potential_A + potential_B

/-- d(c•A)/dt -/
def immediate_A : process_space ℚ ℚ ω Γ
  := finset.sum A.transitions.elems (immediate_process_space conc)
   + (½ : ℚ) • (potential_A ⊘[conc] potential_A)

/-- d(c•A)/dt -/
def immediate_B : process_space ℚ ℚ ω Γ
  := finset.sum B.transitions.elems (immediate_process_space conc)
   + (½ : ℚ) • (potential_B ⊘[conc] potential_B)

/-- d(c•A || c•B)/dt -/
def immediate_proc : process_space ℚ ℚ ω Γ
  := immediate_A + immediate_B + (potential_A ⊘[conc] potential_B)

#eval immediate_proc
