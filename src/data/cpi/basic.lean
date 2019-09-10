/- The primary definitions for the continuous-π calculus-/

import data.non_neg

namespace cpi

/-- A context under which terms may be evaluated.

    Each level of the context holds the arity of the given terms. -/
inductive context
| nil : context
| extend : ℕ → context → context

/-- The set of names within the continuous-π calculus. -/
inductive name : context → Type
| nil    : Π {Γ} {i n : ℕ},  i < n → name (context.extend n Γ)
| extend : Π {Γ} {n : ℕ},   name Γ → name (context.extend n Γ)


/-- A prefix expression. This can either be one of:
  - A communication prefix (send a series of variables on a channel, and then
    recieve, binding $n$ variables).
  - A spontanious or silent prefix: a spontanious reaction with some rate $k$.
    Used to model when a molecule may decompose into a simpler one.
-/
inductive prefix_expr : context → Type
| communicate : Π {Γ}, name Γ → list (name Γ) → ℕ → prefix_expr Γ
| spontanious : Π {Γ}, ℝ≥0 → prefix_expr Γ

namespace prefix_expr
  -- Define some additional notation, and sugar
  notation a `#(` b ` ; ` y `)` := communicate a b y
  notation a `#(` y `)` := communicate a [] y
  notation a `#<` b `>` := communicate a b 0
  notation a `#` := communicate a [] 0

  notation `τ@` k := spontanious k

  /-- Augment a context to be within this term. -/
  def augment : ∀ {Γ}, prefix_expr Γ → context → context
  | ._ (_#(_; y)) Γ := context.extend y Γ
  | ._ (τ@_) Γ := Γ
end prefix_expr

/-- An affinity network.

    This is composed of $arity$ names, and a partial function $f$ which defines
    the affinities between elements of this matrix.
-/
structure affinity := affinity ::
  (arity : ℕ)
  (f : fin arity → fin arity → option ℝ≥0)

/-- The set of species, defining invocation, guarded choice, parallel composition
    and restriction.
-/
mutual inductive species, species.choices
with species : context → Type
| nil : Π {Γ}, species Γ
| choice : Π {Γ : context}, species.choices Γ → species Γ
| parallel : Π {Γ}, species Γ → species Γ → species Γ
| restriction : Π {Γ} (M : affinity), species (context.extend M.arity Γ) → species Γ
with species.choices : context → Type
| nil : Π {Γ}, species.choices Γ
| cons : Π {Γ} (π : prefix_expr Γ), species (prefix_expr.augment π Γ) → species.choices Γ → species.choices Γ

namespace species
  reserve infixr ` |ₛ ` :50
  infixr ` |ₛ ` := parallel

  notation `ν(` m `) ` a := restriction m a
end species

end cpi
