import data.cpi.species data.upair

namespace cpi

variables {ℍ : Type} {ω : context}

/-- The kind of a production, either a species or concretion-/
@[derive decidable_eq, nolint has_inhabited_instance]
inductive kind
| species
| concretion

/-- A transition from a species to some production of a given kind. -/
@[derive decidable_eq, nolint has_inhabited_instance]
inductive label (ℍ : Type) : context → kind → Type
/- From a species to a concretion. Sends $b$ values on channel $a$ and evolves
   into whatever species the concretion applies, substituting $y$ variables
   with the values received. -/
| apply {} {Γ} (a : name Γ) : label Γ kind.concretion

/- Evolution from one species to another species without any other interaction,
   at a specific rate. -/
| spontanious {Γ} (rate : ℍ) : label Γ kind.species

/- Evolution from one species to another, with a rate determined by an affinity
   network. This is converted into a spontanious interaction when the names
   refer to a global affinity network. -/
| of_affinity {} {Γ} (k : upair (name Γ)) : label Γ kind.species

notation `#`:max a:max := label.apply a
notation `τ@'`:max k:max  := label.spontanious k
notation `τ⟨ `:max a `, ` b ` ⟩`:max := label.of_affinity (upair.mk a b)
notation `τ⟨ `:max p ` ⟩`:max := label.of_affinity p

/-- Convert a label to a string. Can use `repr` normally. -/
protected def label.to_string [has_repr ℍ] : ∀ {k}, label ℍ ω k → string
| ._ (# a) := "#" ++ repr a
| ._ (τ@' k) := "τ@" ++ repr k
| ._ (τ⟨ p ⟩) := "τ⟨ " ++ repr p ++ " ⟩"

instance label.has_repr [has_repr ℍ] {k} : has_repr (label ℍ ω k) := ⟨ label.to_string ⟩

/-- Rename all names within a label. -/
def label.rename {Γ Δ} (ρ : name Γ → name Δ) : ∀ {k}, label ℍ Γ k → label ℍ Δ k
| ._ #a := # (ρ a)
| ._ τ@'k := τ@'k
| ._ τ⟨ ab ⟩ := τ⟨ upair.map ρ ab ⟩

lemma label.rename.inj {Γ Δ} {ρ : name Γ → name Δ} (inj : function.injective ρ)
  : ∀ {k}, function.injective (@label.rename ℍ Γ Δ ρ k)
  | ._ #a #b eq := by { cases inj (label.apply.inj eq), from rfl }
  | ._ τ@'k τ@'j rfl := rfl
  | ._ τ⟨ a ⟩ τ⟨ b ⟩ eq := begin
      cases upair.map.inj inj (label.of_affinity.inj eq),
      from rfl
    end
  | ._ τ@'k τ⟨ _ ⟩ eq := by contradiction
  | ._ τ⟨ _ ⟩ τ@'k eq := by contradiction

lemma label.rename_compose {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η)
  : ∀ {k} (l : label ℍ Γ k)
  , label.rename σ (label.rename ρ l) = label.rename (σ ∘ ρ) l
| ._ #a := rfl
| ._ τ@'k := rfl
| ._ τ⟨ ab ⟩ := by simp only [label.rename, upair.map_compose]

lemma label.rename_id {Γ} : ∀ {k} (l : label ℍ Γ k), label.rename id l = l
| ._ #a := rfl
| ._ τ@'k := rfl
| ._ τ⟨ p ⟩ := congr_arg _ (upair.map_identity p)

end cpi

#lint-
