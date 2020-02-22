import data.cpi.species

namespace cpi

variables {ℍ : Type} {ω : context}

/-- A function to look up names within the environment. -/
def lookup (ℍ : Type) (ω Γ : context) := ∀ n, reference n ω → species.choices ℍ ω (context.extend n Γ)

/-- Rename a lookup function, embedding the returned species into another
    context.-/
def lookup.rename {Γ Δ} (ρ : name Γ → name Δ) : lookup ℍ ω Γ → lookup ℍ ω Δ
| f n r := species.rename (name.ext ρ) (f n r)

/-- Rewrite lemma for when lookups get expanded incorrectly. -/
lemma lookup.rename.def {Γ Δ} (ρ : name Γ → name Δ) (ℓ : lookup ℍ ω Γ)
  : (λ n r, species.rename (name.ext ρ) (ℓ n r)) = lookup.rename ρ ℓ
  := rfl

lemma lookup.rename.inj {Γ Δ} {ρ : name Γ → name Δ} (inj : function.injective ρ)
  : function.injective (@lookup.rename ℍ ω Γ Δ ρ)
| x y eq := funext $ λ n, funext $ λ r, begin
  have : species.rename (name.ext ρ) (x n r) = species.rename (name.ext ρ) (y n r)
    := congr_fun (congr_fun eq n) r,
  from species.rename.inj (name.ext.inj inj) this,
end

lemma lookup.rename_compose {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η)
  : ∀ (ℓ : lookup ℍ ω Γ)
  , lookup.rename σ (lookup.rename ρ ℓ) = lookup.rename (σ ∘ ρ) ℓ
| f := funext $ λ n, funext $ λ r, begin
  simp only [lookup.rename, function.comp],
  rw [species.rename_compose (name.ext ρ) (name.ext σ) (f n r), name.ext_comp],
end

end cpi

#lint-
