/- The primary definitions for the continuous-π calculus-/

import data.non_neg
import tactic.sanity_check

import data.multiset

namespace cpi

/-- A context under which terms may be evaluated.

    Each level of the context holds the arity of the given terms. -/
inductive context
| nil : context
| extend : ℕ → context → context

/-- The set of names within the continuous-π calculus. -/
inductive name : context → Type
| nil    {Γ} {n : ℕ} : fin n → name (context.extend n Γ)
| extend {Γ} {n : ℕ} : name Γ → name (context.extend n Γ)

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
notation a `#(`:40 b ` ; ` y `)` := prefix_expr.communicate a b y
notation a `#(`:40 y `)` := prefix_expr.communicate a [] y
notation a `#<`:40 b `>` := prefix_expr.communicate a b 0
notation a `#`:40 := prefix_expr.communicate a [] 0

notation `τ@` k:40 := prefix_expr.spontanious k

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
| nil {Γ} : species Γ
| choice {Γ} : species.choices Γ → species Γ
| parallel {Γ} : species Γ → species Γ → species Γ
| restriction {Γ} (M : affinity) : species (context.extend M.arity Γ) → species Γ
with species.choices : context → Type
| nil {Γ} : species.choices Γ
| cons {Γ} {f} (π : prefix_expr Γ f) : species (f Γ) → species.choices Γ → species.choices Γ

reserve infixr ` |ₛ ` :50
infixr ` |ₛ ` := species.parallel

notation `ν(` M `) ` A := species.restriction M A

/-- The set of processes. Defined as one or more species, each with a
    non-negative concentration.

    The context parameter represents the "global affinity network", in which
    all processes are evaluated. -/
inductive process : context → Type
| one      {Γ} : ℝ≥0 → species Γ → process Γ
| parallel {Γ} : process Γ → process Γ → process Γ

infix ` • `:60 := process.one
infixr ` |ₚ `:50 := process.parallel

namespace tactic
  open tactic
  open well_founded_tactics

  /-- An alternative version of dec_tac which also unfolds .fst indexing.

      This is required for the various proofs which skip the implicit context
      argument. -/
  meta def fst_dec_tac : tactic unit := abstract $ do
      clear_internals,
      unfold_wf_rel,
      process_lex (unfold_sizeof >> try (tactic.dunfold_target [``psigma.fst])
                >> cancel_nat_add_lt >> trivial_nat_lt)
end tactic

end cpi

-- | For sanity checking only. This takes a long time to run normally.
-- run_cmd sanity_check
-- #sanity_check
