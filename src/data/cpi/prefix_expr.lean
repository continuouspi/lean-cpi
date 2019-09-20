import data.non_neg
import data.cpi.name

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi

/-- A prefix expression. This can either be one of:

  - A communication prefix (send a series of variables on a channel, and then
    recieve, binding $n$ variables).

  - A spontanious or silent prefix: a spontanious reaction with some rate $k$.
    Used to model when a molecule may decompose into a simpler one.

  The prefix is parameterised by two contexts: the context it exists in, and the
  context resulting from binding this prefix expression. While it would be
  possible to do this with some "augment" function, it ends up complicating the
  type system a little, as you end up with weird unification constraints.
-/
inductive prefix_expr : context → (context → context) → Type
| communicate {Γ} (a :  name Γ) (b : list (name Γ)) (y : ℕ) : prefix_expr Γ (context.extend y)
| spontanious {Γ} (k : ℝ≥0) : prefix_expr Γ id

-- Define some additional notation, and sugar
notation a `#(` b ` ; ` y `)` := prefix_expr.communicate a b y
notation a `#(` y `)` := prefix_expr.communicate a [] y
notation a `#<` b `>` := prefix_expr.communicate a b 0
notation a `#` := prefix_expr.communicate a [] 0

notation `τ@`:max k:max := prefix_expr.spontanious k


namespace prefix_expr
  /-- Apply a renaming function to a prefix. -/
  def rename : Π {Γ Δ : context} {f}, (name Γ → name Δ) → prefix_expr Γ f → prefix_expr Δ f
    | Γ Δ f ρ (a#(b; y)) := (ρ a)#(list.map ρ b; y)
    | Γ Δ f ρ τ@k := τ@k

  /-- Scope extension for prefix expressions. Given a renaming function, return
      the same function lifted for the variables bound by this prefix. -/
  def ext :
    Π {Γ Δ η : context} {f} (π : prefix_expr η f)
    , (name Γ → name Δ)
    → name (f Γ) → name (f Δ)
  | Γ Δ ._ ._ (a#(b; y)) ρ α := name.ext ρ α
  | Γ Δ ._ ._ τ@k ρ α := ρ α

  /-- Extending with the identity does nothing. -/
  lemma ext_identity :
    ∀ {Γ η : context} {f} (π : prefix_expr η f) (α : name (f Γ))
    , ext π id α = α
  | Γ η ._ (a#(b; y)) α := name.ext_identity α
  | Γ η ._ τ@k name := rfl

  /-- Extending with the identity yields the identity function. -/
  lemma ext_id : ∀ {Γ η : context} {f} (π : prefix_expr η f), @ext Γ Γ η f π id = id
  | Γ η f π := funext (ext_identity π)

  /-- Composing extensions is equivalent extending a composition. -/
  lemma ext_compose :
    ∀ {Γ Δ η φ} {f} (ρ : name Γ → name Δ) (σ : name Δ → name η)
      (π : prefix_expr φ f) (α : name (f Γ))
    , ext π σ (ext π ρ α) = ext π (σ ∘ ρ) α
  | Γ Δ η φ f ρ σ (a#(b; y)) α := name.ext_compose ρ σ α
  | Γ Δ η φ f ρ σ τ@k α := rfl

  /-- Composing extensions is equivalent extending a composition. -/
  lemma ext_comp :
    ∀ {Γ Δ η φ} {f} (ρ : name Γ → name Δ) (σ : name Δ → name η) (π : prefix_expr φ f)
    , (ext π σ ∘ ext π ρ) = ext π (σ ∘ ρ)
  | Γ Δ η φ f ρ σ π := funext (ext_compose ρ σ π)

  /-- Extending with a renamed prefix has the same effect as the original one. -/
  lemma rename_ext :
    ∀ {Γ Δ η φ} {f} (ρ : name Γ → name Δ) (σ : name η → name φ) (π : prefix_expr Γ f)
    , @ext η φ Γ f π σ = (ext (rename ρ π) σ)
  | Γ Δ η φ f ρ σ (a#(b; y)) := funext (λ α, rfl)
  | Γ Δ η φ f ρ σ τ@k := funext (λ α, rfl)

  /-- Renaming with the identity function does nothing. -/
  lemma rename_id : ∀ {Γ} {f} (π : prefix_expr Γ f), rename id π = π
  | Γ ._ (a#(b; y)) := by simp [rename]
  | Γ ._ τ@k := rfl

  /-- Renaming twice is the same as renaming with a composed function. -/
  lemma rename_compose :
    ∀ {Γ Δ η} {f} (ρ : name Γ → name Δ) (σ : name Δ → name η) (π : prefix_expr Γ f)
    , rename σ (rename ρ π) = rename (σ ∘ ρ) π
  | Γ Δ η f ρ σ (a#(b; y)) := by simp [rename]
  | Γ Δ η f ρ σ (τ@_) := rfl
end prefix_expr

end cpi

#sanity_check
