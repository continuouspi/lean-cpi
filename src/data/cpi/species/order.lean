import data.cpi.species.basic

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi
namespace species

open whole

private noncomputable def eq_decidable {Γ} {k} (A B : whole k Γ) : decidable (A = B) := begin
  induction A,

  case nil { cases B; simp only []; apply_instance },
  case parallel : _ A₁ A₂ ih_1 ih_2 {
    cases B; simp only []; try { apply_instance },
    case parallel : B₁ B₂ { from @and.decidable _ _ (ih_1 B₁) (ih_2 B₂) }
  },
  case restriction : _ M A ih {
    cases B; simp only []; try { apply_instance },
    case restriction : M' B {
      cases (by apply_instance : decidable (M = M')),
      case is_true : h { subst h, simp, from ih B },
      case is_false : h { from decidable.is_false (λ x, h x.left) }
     }
  },
  case choice : _ As ih {
    cases B; simp only []; try { apply_instance },
    case choice : As' { from ih As' }
  },
  case whole.empty { cases B; simp only []; apply_instance },
  case whole.cons : _ f π A As ih_a ih_as {
    cases B; simp only []; try { apply_instance },
    case whole.cons : f' π' A' As' {
      have h : decidable (prefix_expr.wrap.intro π = prefix_expr.wrap.intro π'),
        apply_instance,

      cases h,
      case is_false : p {
        from is_false (λ x, begin
          simp only [] at p,
          have : f = f' ∧ π == π' := ⟨ x.left, x.right.left ⟩,
          contradiction
        end)
      },
      case is_true : p {
        simp only [] at p,
        have : f = f' := p.left, subst this,
        simp [p],

        from @and.decidable _ _ (ih_a A') (ih_as As')
      }
    }
  }
end

noncomputable instance {Γ} : decidable_eq (species Γ) := eq_decidable

end species
end cpi

#sanity_check
