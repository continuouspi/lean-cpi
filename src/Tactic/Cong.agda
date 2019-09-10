module Tactic.Cong where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≗_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _≡˘⟨_⟩_;_∎)

open import Data.Bool using (Bool; true; false; _∨_ )
open import Data.List as List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using ( _,_; _×_ )
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_; id; _∘_)
open import Relation.Nullary using (yes; no)

open import Reflection

private
  has-meta : Term → Bool
  has-meta-sort : Sort → Bool
  has-meta-args : List (Arg Term) → Bool
  has-meta-clauses : List Clause → Bool

  has-meta (var _ args) = has-meta-args args
  has-meta (con _ args) = has-meta-args args
  has-meta (def _ args) = has-meta-args args
  has-meta (lam _ (abs _ bod)) = has-meta bod
  has-meta (pat-lam cs args) = has-meta-clauses cs ∨ has-meta-args args
  has-meta (pi (arg _ ty) (abs _ bod)) = has-meta ty ∨ has-meta bod
  has-meta (sort s) = has-meta-sort s
  has-meta (lit _) = false
  has-meta (meta _ _) = true
  has-meta unknown = false

  has-meta-sort (set t) = has-meta t
  has-meta-sort (lit n) = false
  has-meta-sort unknown = false

  has-meta-args [] = false
  has-meta-args ((arg _ x) ∷ xs) = has-meta x ∨ has-meta-args xs

  has-meta-clauses [] = false
  has-meta-clauses (clause _ t ∷ xs) = has-meta t ∨ has-meta-clauses xs
  has-meta-clauses (absurd-clause _ ∷ xs) = has-meta-clauses xs

  ensure-no-meta : String → Term → TC ⊤
  ensure-no-meta msg term =
    case has-meta term of λ
      { true → typeError ( strErr msg ∷ termErr term ∷ [] )
      ; false → return tt
      }

  ext : (ℕ → ℕ) → ℕ → ℕ
  ext ρ zero = zero
  ext ρ (suc x) = suc (ρ x)

  increase : Pattern → (ℕ → ℕ) → ℕ → ℕ
  increases : List (Arg Pattern) → (ℕ → ℕ) → ℕ → ℕ
  increase (con c ps) = increases ps
  increase dot = ext
  increase (var _) = ext
  increase (lit _) = id
  increase (proj f) = id
  increase absurd = id

  increases [] ρ = ρ
  increases (arg _ x ∷ xs) ρ = increases xs (increase x ρ)

  -- Variable renaming. Apply some renaming function over terms in a scope aware context.
  rename : Term → (ℕ → ℕ) → Term
  rename-sort : Sort → (ℕ → ℕ) → Sort
  rename-args : List (Arg Term) → (ℕ → ℕ) → List (Arg Term)
  rename-clauses : List Clause → (ℕ → ℕ) → List Clause
  rename-clause : Clause → (ℕ → ℕ) → Clause
  rename-arg : Arg Term → (ℕ → ℕ) → Arg Term
  rename-abs : Abs Term → (ℕ → ℕ) → Abs Term

  rename (var x args) ρ = var (ρ x) (rename-args args ρ)
  rename (con c args) ρ = con c (rename-args args ρ)
  rename (def f args) ρ = def f (rename-args args ρ)
  rename (lam v b) ρ = lam v (rename-abs b ρ)
  rename (pat-lam cs args) ρ = pat-lam (rename-clauses cs ρ) (rename-args args ρ)
  rename (pi a b) ρ = pi (rename-arg a ρ) (rename-abs b ρ)
  rename (sort s) ρ = sort (rename-sort s ρ)
  rename (lit l) ρ = lit l
  rename (meta x x₁) ρ = meta x x₁
  rename unknown ρ = unknown

  rename-sort (set t) ρ = set (rename t ρ)
  rename-sort (lit n) ρ = lit n
  rename-sort unknown ρ = unknown

  rename-args [] ρ = []
  rename-args (x ∷ xs) ρ = rename-arg x ρ ∷ rename-args xs ρ

  rename-arg (arg i x) ρ = arg i (rename x ρ)
  rename-abs (abs x v) ρ = abs x (rename v (ext ρ))

  rename-clauses [] ρ = []
  rename-clauses (x ∷ xs) ρ = rename-clause x ρ ∷ rename-clauses xs ρ

  rename-clause (clause ps t) ρ = clause ps (rename t (increases ps ρ))
  rename-clause (absurd-clause ps) ρ = absurd-clause ps

  -- Replacement: Replace any occurence of a pattern with a new one.
  replace : Term → Term → Term → (ℕ → ℕ) → Term
  replace-impl : Term → Term → Term → (ℕ → ℕ) → Term
  replace-sort : Sort → Term → Term → (ℕ → ℕ) → Sort
  replace-args : List (Arg Term) → Term → Term → (ℕ → ℕ) → List (Arg Term)
  replace-clauses : List Clause → Term → Term → (ℕ → ℕ) → List Clause
  replace-clause : Clause → Term → Term → (ℕ → ℕ) → Clause
  replace-arg : Arg Term → Term → Term → (ℕ → ℕ) → Arg Term
  replace-abs : Abs Term → Term → Term → (ℕ → ℕ) → Abs Term

  replace x pat rep ρ with x ≟ pat
  ...                | yes _ = rename rep ρ
  ...                | no _ = replace-impl x pat rep ρ

  replace-impl (var x args) pat rep ρ = var (ρ x) (replace-args args pat rep ρ)
  replace-impl (con c args) pat rep ρ = con c (replace-args args pat rep ρ)
  replace-impl (def f args) pat rep ρ = def f (replace-args args pat rep ρ)
  replace-impl (lam v b) pat rep ρ = lam v (replace-abs b pat rep ρ)
  replace-impl (pat-lam cs args) pat rep ρ = pat-lam (replace-clauses cs pat rep ρ) (replace-args args pat rep ρ)
  replace-impl (pi a b) pat rep ρ = pi (replace-arg a pat rep ρ) (replace-abs b pat rep ρ)
  replace-impl (sort s) pat rep ρ = sort (replace-sort s pat rep ρ)
  replace-impl (lit l) pat rep ρ = lit l
  replace-impl (meta x x₁) pat rep ρ = meta x x₁
  replace-impl unknown pat rep ρ = unknown

  replace-sort (set t) pat rep ρ = set (replace t pat rep ρ)
  replace-sort (lit n) pat rep ρ = lit n
  replace-sort unknown pat rep ρ = unknown

  replace-args [] pat rep ρ = []
  replace-args (x ∷ xs) pat rep ρ = replace-arg x pat rep ρ ∷ replace-args xs pat rep ρ

  replace-arg (arg i x) pat rep ρ = arg i (replace x pat rep ρ)
  replace-abs (abs x v) pat rep ρ = abs x (replace v pat rep (ext ρ))

  replace-clauses [] pat rep ρ = []
  replace-clauses (x ∷ xs) pat rep ρ = replace-clause x pat rep ρ ∷ replace-clauses xs pat rep ρ

  replace-clause (clause ps t) pat rep ρ = clause ps (replace t pat rep (increases ps ρ))
  replace-clause (absurd-clause ps) pat rep ρ = absurd-clause ps

  get-eq : String → Type → TC (Type × Type × Type × Type)
  get-eq _ (def (quote _≡_) (arg _ lvl ∷ arg _ ty ∷ arg _ l ∷ arg _ r ∷ [])) = return (lvl , ty , l , r)
  get-eq msg term = typeError ( strErr msg ∷ termErr term ∷ [] )

  arg' arg- : Term → Arg Term
  arg' = arg (arg-info hidden relevant)
  arg- = arg (arg-info visible relevant)

macro
  -- | Apply Eq.cong, but automatically deriving the required term-generating
  -- | function.
  --
  -- This is designed to be used in equational reasoning blocks. Consider the
  -- following:
  --
  -- begin
  --   f x + 5
  -- ≡⟨ Eq.cong (λ x → f x + 5) eq ⟩ -- (eq : x ≡ y)
  --   f y + 6
  -- ∎
  --
  -- One may now write
  --
  -- begin
  --   f x + 5
  -- ≡⟨ ▸ eq ⟩
  --   f y + 6
  -- ∎
  --
  -- This simply inspects the types of the argument, and the desired type, and
  -- generates a function which replaces all occurrences of x within the goal.
  --
  -- There's definitely smarter ways of doing this (see [1]) for a superior
  -- implementation, but this is sufficient for now.
  --
  -- [1]: https://github.com/UlfNorell/agda-prelude/blob/master/src/Tactic/Cong.agda
  ▸_ : Term → Term → TC ⊤
  ▸_ rw hole = do
    big <- inferType hole >>= normalise
    small <- inferType rw >>= normalise
    (big-lvl   , big-ty   , left , right) ← get-eq "Expected equality for goal" big
    (small-lvl , small-ty , from , to   ) ← get-eq "Expected equality for rewrite rule" small
    ensure-no-meta "Left hand side of goal cannot have meta-variables" left

  -- TODO: Allow using from or to
    ensure-no-meta "Left hand side of rewrite cannot have meta-variables" from

    let repl = replace (rename left suc) (rename from suc) (var 0 []) id
        lam = lam visible (abs "x" repl)
        cong = def (quote Eq.cong) ( arg' small-lvl ∷ arg' small-ty
                                   ∷ arg' big-lvl ∷ arg' big-ty
                                   ∷ arg- lam ∷ arg' from ∷ arg' to ∷ arg- rw
                                   ∷ [])
        new-right = replace left from to id

    debugPrint "Derived a type" 3
      ( strErr "Derived for" ∷ termErr big
      ∷ strErr " ⇒ " ∷ termErr cong ∷ [] )

    -- t' ← inferType lam
    -- t ← inferType cong
    -- debugPrint "Additional info" 3
    --   ( strErr "\nFrom    :" ∷ termErr from
    --   ∷ strErr "\nTo      :" ∷ termErr to
    --   ∷ strErr "\nEq      :" ∷ termErr rw
    --   ∷ strErr "\nWhole   :" ∷ termErr cong ∷ strErr ":" ∷ termErr t
    --   ∷ [])

    unify hole cong
    unify right new-right -- Probably redundant, but good to force.
