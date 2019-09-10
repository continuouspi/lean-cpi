module Data.CPi.Base where

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open import Function using (id)

-- | A context under whith terms may be evaluated.
--
-- Each level of the context holds the arity of the variable vector.
data Context : Set where
  Nil : Context
  Extend : ℕ → Context → Context

-- | A name within a given context.
data Name : Context → Set where
  Nil : ∀ {Γ} {i n : ℕ} → i < n → Name (Extend n Γ)
  Extend : ∀ {Γ} {n : ℕ} → Name Γ → Name (Extend n Γ)

-- | A prefix expression. This can either be one of:
--
--  - A communication prefix (send a series of variables on a channel, and then
--    recieve, binding $n$ variables).
--
--  - A spontanious or silent prefix: a spontanious reaction with some rate $k$.
--    Used to model when a molecule may decompose into a simpler one.

-- The prefix is parameterised by the context it is evaluated within, and an
-- "augmenting function", which extends any context with whatever variables this
-- prefix binds.
--
-- This function could be derived from the structure of the type, but it ends up
-- causing problems when need to show that substituting preserves the
-- augmentation.
data Prefix : Context → (Context → Context) → Set where
  _#[_,_] : ∀ {Γ} (a : Name Γ) (b : List (Name Γ)) (y : ℕ) → Prefix Γ (Extend y)
  τ#_ : ∀ {Γ} (k : ℕ) → Prefix Γ id

-- syntax Communicate a b y = a #[ b , y ]
-- syntax Communicate a [] y = a #[ y ]
-- syntax Communicate a b 0 = a #< b >
-- syntax Communicate a [] 0 = a #

-- syntax Spontanious k = τ# k

-- | An affinity network.

-- This is composed of $arity$ names, and a partial function $f$ which defines
-- the affinities between elements of this matrix.
record Affinity : Set where
  field
    arity : ℕ
    f : Fin arity → Fin arity → Maybe ℕ

-- | A species, defining guarded choice, parallel composition and restriction.
data Species : Context → Set where
  Nil : ∀ {Γ} → Species Γ
  Choice : ∀ {Γ} → List (Σ[ f ∈ (Context → Context)] (Prefix Γ f × Species (f Γ))) → Species Γ
  _|ₛ_ : ∀ {Γ} → Species Γ → Species Γ → Species Γ
  ν[_]_ : ∀ {Γ} (M : Affinity) → Species (Extend (Affinity.arity M) Γ) → Species Γ
