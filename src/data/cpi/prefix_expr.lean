import data.cpi.name
import data.non_neg

namespace cpi

/-- A prefix expression. This can either be one of:
  - A communication prefix (send a series of variables on a channel, and then
    recieve, binding $n$ variables).
  - A spontanious or silent prefix: a spontanious reaction with some rate $k$.
    Used to model when a molecule may decompose into a simpler one.
-/
inductive prefix_expr
| communicate : name → list name → ℕ → prefix_expr
| spontanious : ℝ≥0 → prefix_expr

namespace prefix_expr
  -- Define some additional notation, and sugar
  notation a `#(` b ` ; ` y `)` := communicate a b y
  notation a `#(` y `)` := communicate a [] y
  notation a `#<` b `>` := communicate a b 0
  notation a `#` := communicate a [] 0

  notation `τ@` k := spontanious k

  section free_variables
    /-- Is this prefix expression valid within the current context? -/
    def well_formed : context → prefix_expr →  Prop
    | Γ (a#(ns; _)) := name.well_formed Γ a ∧ ∀ x ∈ ns, name.well_formed Γ x
    | Γ τ@_ := true

    def subst : (lvl → lvl) → prefix_expr → prefix_expr
    | ρ (a#(b; y)) := (name.subst ρ a)#(list.map (name.subst ρ) b; y)
    | ρ τ@k := τ@k

    def subst.well_formed :
      Π {Γ Δ : context} {ρ : lvl → lvl}
      , (∀ {α : name}, name.well_formed Γ α → name.well_formed Δ (name.subst ρ α))
      → ∀ {π : prefix_expr}, well_formed Γ π → well_formed Δ (subst ρ π)
    | Γ Δ ρ imp (a#(b; _)) wf := begin
        unfold well_formed subst at wf ⊢,
        cases wf with wf_a wf_b,
        have h : ∀ (x : name), x ∈ list.map (name.subst ρ) b → name.well_formed Δ x,
          simp only [and_imp, exists_imp_distrib, list.mem_map, list.map],
          assume (x y : name) (mem : y ∈ b) (eq : name.subst ρ y = x),
          subst eq, from imp (wf_b y mem),

        from and.intro (imp wf_a) h
      end
    | Γ Δ ρ imp (τ@k) wf := by unfold well_formed at wf ⊢

    /-- Migrate a variable into the scope of this term, lifting the level if
        required. -/
    def ext : (lvl → lvl) → prefix_expr → lvl → lvl
    | ρ (a#(_; _)) := name.ext ρ
    | ρ (τ@_) := ρ

    /-- Augment a context to be within this term. -/
    def augment : context → prefix_expr → context
    | Γ (_#(_; y)) := context.extend y Γ
    | Γ (τ@_) := Γ

    /-- Prove that extension/augmenting preserves the well-formed property. -/
    theorem ext.well_formed :
      Π {Γ Δ : context} {ρ : lvl → lvl}
      , (∀ (α : name), name.well_formed Γ α → name.well_formed Δ (name.subst ρ α))
      → ∀ {π : prefix_expr} (α : name), name.well_formed (augment Γ π) α → name.well_formed (augment Δ π) (name.subst (ext ρ π) α)
      | Γ Δ ρ imp (a#(b; y)) α := by { unfold augment ext, from name.ext.well_formed imp α }
      | Γ Δ ρ imp (τ@k) α := by { unfold augment ext, from imp α }

    /-- Augmenting with substituted prefix has the same effect as the base one. -/
    theorem subst_augment : ∀ {Γ ρ π}, augment Γ π = augment Γ (subst ρ π)
    | Γ ρ (_#(_; _)) := by { unfold augment subst }
    | Γ ρ (τ@_) := by { unfold augment subst }

    /-- Extending with substituted prefix has the same effect as the base one. -/
    theorem subst_ext : ∀ {ρ σ π}, ext σ π = ext σ (subst ρ π)
    | Γ ρ (_#(_; _)) := by { unfold ext subst }
    | Γ ρ (τ@_) := by { unfold ext subst }

  end free_variables
end prefix_expr

end cpi
