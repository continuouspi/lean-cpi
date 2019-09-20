import tactic.sanity_check

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi

/-- A context under which terms may be evaluated.

    Each level of the context holds the arity of the vector defined at that
    point. -/
inductive context
| nil : context
| extend : ℕ → context → context

/-- The set of names within the continuous-π calculus. -/
inductive name : context → Type
| zero   {Γ} {n : ℕ} : fin n → name (context.extend n Γ)
| extend {Γ} {n : ℕ} : name Γ → name (context.extend n Γ)

namespace name
  /-- Scope extension for names. Given a renaming function, return the same
      function lifted one level.-/
  def ext :
    Π {Γ Δ : context}
    , (name Γ → name Δ)
    → ∀ {n : ℕ}, name (context.extend n Γ) → name (context.extend n Δ)
    | Γ Δ ρ n (zero idx) := zero idx
    | Γ Δ ρ n (extend x) := extend (ρ x)

  /-- Extending with the identity does nothing. -/
  lemma ext_identity :
    ∀ {Γ : context} {n : ℕ} (α : name (context.extend n Γ))
    , ext id α = α
  | Γ n (zero lt) := rfl
  | Γ n (extend α) := rfl

  /-- Extending with the identity yields the identity function. -/
  lemma ext_id : ∀ {Γ : context} {n : ℕ}, @ext Γ Γ id n = id
  | Γ n := funext ext_identity

  /-- Composing extensions is equivalent extending a composition. -/
  lemma ext_compose :
    ∀ {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η) {n : ℕ} (α : name (context.extend n Γ))
    , ext σ (ext ρ α) = ext (σ ∘ ρ) α
  | Γ Δ η ρ σ n (zero lt) := rfl
  | Γ Δ η ρ σ n (extend α) := rfl

  /-- Composing extensions is equivalent extending a composition. -/
  lemma ext_comp :
    ∀ {Γ Δ η} (ρ : name Γ → name Δ) (σ : name Δ → name η) {n : ℕ}
    , (ext σ ∘ ext ρ) = @ext _ _ (σ ∘ ρ) n
  | Γ Δ η ρ σ n := funext (ext_compose ρ σ)

  /-- Extending then renaming with an extended function, is equivalent to
      renaming then extending. -/
  lemma ext_extend :
    ∀ {Γ Δ} {n : ℕ} (ρ : name Γ → name Δ)
    , (ext ρ ∘ extend) = (@extend Δ n ∘ ρ)
  | Γ Δ n ρ := funext (λ x, rfl)

  /-- Swap the two topmost variables. Used for exchange of ν terms. -/
  def swap {Γ} {M N : ℕ}
    : name (context.extend M (context.extend N Γ))
    → name (context.extend N (context.extend M Γ))
  | (zero lt) := extend (zero lt)
  | (extend (zero lt)) := zero lt
  | (extend (extend n)) := extend (extend n)

  /-- A twice-extended renaming function can be applied before or after a swap.
   -/
  lemma swap_ext_ext {Γ Δ} {ρ : name Γ → name Δ} {m n : ℕ}
    : (ext (ext ρ) ∘ swap)
    = (swap ∘ @ext _ _ (@ext _ _ ρ m) n) := funext $ λ α,
      match α with
      | zero p := by simp [swap, ext]
      | extend (zero lt) := by simp [swap, ext]
      | extend (extend _) := by simp [swap, ext]
      end

  /-- Incrementing and swapping, is just the same as incrementing everything
      above 0. -/
  lemma swap_comp_extend {Γ} {m n : ℕ}
    : (@name.swap Γ m n ∘ name.extend) = (name.ext name.extend) := funext $ λ α,
      match α with
      | zero idx := by simp [swap, ext]
      | extend n := by simp [swap, ext]
      end

  /-- Incrementing everything above 0 and swapping is the same as just
      incrementing above 0. -/
  lemma swap_comp_ext_extend {Γ} {m n : ℕ}
    : (@name.swap Γ m n ∘ name.ext name.extend) = name.extend := funext $ λ α,
      match α with
      | zero idx := by simp [swap, ext]
      | extend n := by simp [swap, ext]
      end
end name

end cpi

#sanity_check
