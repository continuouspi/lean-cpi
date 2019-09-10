module Data.CPi.Var where

open import Data.CPi.Base

import Data.List as List
import Data.List.Properties as List
import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; refl)

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _≡˘⟨_⟩_;_∎)
open import Data.Nat using (ℕ)
open import Function using (id; _∘_)
open import Level using (0ℓ)

open import Relation.Binary.PropositionalEquality using (_≗_)

open import Tactic.Cong

module Name-v where
  -- | Scope extension for names.
  --
  -- Given a renaming function, lift it one level, making it usable in a nested
  -- context.
  ext : ∀ {Γ Δ} → (Name Γ → Name Δ)
      → {n : ℕ} → Name (Extend n Γ) → Name (Extend n Δ)
  ext ρ (Nil lt) = Nil lt
  ext ρ (Extend x) = Extend (ρ x)

  -- | Extending with the identity does nothing.
  ext-id : ∀ {Γ} {n} → ext {Γ} id {n} ≗ id
  ext-id (Nil x) = refl
  ext-id (Extend α) = refl

  -- | Function extensionality over extensions.
  ext-cong : ∀ {Γ Δ} {ρ σ : Name Γ → Name Δ} {n}
           → ρ ≗ σ → ext ρ {n} ≗ ext σ
  ext-cong ext (Nil x) = refl
  ext-cong ext (Extend α) = ▸ ext α

  -- | Composing extensions is equivalent to extending a composition.
  ext-compose : ∀ {Γ Δ η} {n} (ρ : Name Γ → Name Δ) (σ : Name Δ → Name η)
              → (ext σ ∘ ext ρ) ≗ ext (σ ∘ ρ) {n}
  ext-compose σ ρ (Nil x) = refl
  ext-compose σ ρ (Extend x) = refl

  -- | Extending the renaming with an extended function is equivalent to
  -- | renaming then extending.
  ext-extend : ∀ {Γ Δ} {n} (ρ : Name Γ → Name Δ)
             → (ext ρ {n} ∘ Extend) ≗ (Extend ∘ ρ)
  ext-extend ρ x = refl

module Prefix-v where
  -- Rename variables within a prefix.
  subst : ∀ {Γ Δ} {f} (ρ : Name Γ → Name Δ) → Prefix Γ f → Prefix Δ f
  subst ρ (a #[ b , y ]) = ρ a #[ List.map ρ b , y ]
  subst ρ (τ# x) = τ# x

  -- Scope extension for prefixes.
  --
  -- Given a renaming function, lift it if appropriate, making it usable in a
  -- within a context bound by this prefix.
  ext : ∀ {Γ Δ η} {f} (π : Prefix η f) (ρ : Name Γ → Name Δ)
      → Name (f Γ) → Name (f Δ)
  ext (a #[ b , y ]) ρ = Name-v.ext ρ
  ext (τ# k) ρ = ρ

  -- | Extending with the identity does nothing.
  ext-id : ∀ {Γ η} {f} (π : Prefix η f) → ext {Γ} π id ≗ id
  ext-id (a #[ b , y ]) α = Name-v.ext-id α
  ext-id (τ# k) α = refl

  -- | Function extensionality over extensions.
  ext-cong : ∀ {Γ Δ η} {f} {ρ σ : Name Γ → Name Δ} (π : Prefix η f)
           → ρ ≗ σ → ext π ρ ≗ ext π σ
  ext-cong (a #[ b , y ]) ext = Name-v.ext-cong ext
  ext-cong (τ# k) ext = ext

  -- | Composing extensions is equivalent to extending a composition.
  ext-compose : ∀ {Γ Δ η ϕ} {f} (ρ : Name Γ → Name Δ) (σ : Name Δ → Name η)
              → (π : Prefix ϕ f)
              → (ext π σ ∘ ext π ρ) ≗ ext π (σ ∘ ρ)
  ext-compose ρ σ (a #[ b , y ]) α = Name-v.ext-compose ρ σ α
  ext-compose ρ σ (τ# k) α = refl

  -- | Extending with a substituted prefix has the same effect as using the
  -- | original.
  subst-ext : ∀ {Γ Δ η ϕ} {f} (ρ : Name Γ → Name Δ)
                (π : Prefix Γ f)
              → ext {η} {ϕ} π ≗ ext (subst ρ π)
  subst-ext ρ (a #[ b , y ]) α = refl
  subst-ext ρ (τ# k) α = refl

  -- | Function extensionality over substitution.
  subst-cong : ∀ {Γ Δ} {f} {ρ σ : Name Γ → Name Δ}
              → ρ ≗ σ → subst {Γ} {Δ} {f} ρ ≗ subst σ
  subst-cong {_} {_} {_} {ρ} {σ} ext (a #[ b , y ]) =
    begin
      ρ a #[ List.map ρ b , y ]
    ≡⟨ ▸ ext a ⟩
      σ a #[ List.map ρ b , y ]
    ≡⟨ ▸ List.map-cong ext b ⟩
      σ a #[ List.map σ b , y ]
    ∎
  subst-cong ext (τ# k) = refl

  -- | Substituting with the identity function does nothing.
  subst-id : ∀ {Γ} {f} (π : Prefix Γ f) → subst id π ≡ π
  subst-id (a #[ b , y ]) =
    begin
      id a #[ List.map id b , y ]
    ≡⟨ ▸ List.map-id b ⟩
      id a #[ id b , y ]
    ∎
  subst-id (τ# k) = refl

  -- | Substituting twice is the same as substiting on a composed function.
  -- | Composing extensions is equivalent to extending a composition.
  subst-compose : ∀ {Γ Δ η} {f} (ρ : Name Γ → Name Δ) (σ : Name Δ → Name η)
                → (subst σ ∘ subst ρ) ≗ subst {Γ} {η} {f} (σ ∘ ρ)
  subst-compose {Γ} {Δ} {η} ρ σ (a #[ b , y ]) =
    begin
      σ (ρ a) #[ List.map σ (List.map ρ b) , y ]
    ≡˘⟨ Eq.cong (σ (ρ a) #[_, y ]) (List.map-compose b) ⟩
      σ (ρ a) #[ List.map (σ ∘ ρ) b , y ]
    ∎
  subst-compose ρ σ (τ# k) = refl

module Species-v where
  -- | Rename variables within a species.
  subst : ∀ {Γ Δ} (ρ : Name Γ → Name Δ) → Species Γ → Species Δ
  subst-choice : ∀ {Γ Δ} (ρ : Name Γ → Name Δ)
               → List (Σ[ f ∈ (Context → Context)] (Prefix Γ f × Species (f Γ)))
               → List (Σ[ f ∈ (Context → Context)] (Prefix Δ f × Species (f Δ)))

  subst ρ Nil = Nil
  subst ρ (Choice As) = Choice (subst-choice ρ As)
  subst ρ (A |ₛ B) = subst ρ A |ₛ subst ρ B
  subst ρ (ν[ M ] A) = ν[ M ] subst (Name-v.ext ρ) A

  -- Unfolded, as otherwise we cannot prove termination.
  subst-choice ρ [] = []
  subst-choice ρ ((f , π , A ) ∷ As)
    = (f , Prefix-v.subst ρ π , subst (Prefix-v.ext π ρ) A)
    ∷ subst-choice ρ As

  -- | Function extensionality over substitution.
  subst-cong : ∀ {Γ Δ} {ρ σ : Name Γ → Name Δ} → ρ ≗ σ → subst ρ ≗ subst σ
  subst-cong-choice : ∀ {Γ Δ} {ρ σ : Name Γ → Name Δ} → ρ ≗ σ → subst-choice ρ ≗ subst-choice σ
  subst-cong _ Nil = refl
  subst-cong {_} {_} {ρ} {σ} ext (Choice As) = ▸ subst-cong-choice ext As
  subst-cong {_} {_} {ρ} {σ} ext (A |ₛ B) =
    begin
      subst ρ A |ₛ subst ρ B
    ≡⟨ ▸ subst-cong ext A ⟩
      subst σ A |ₛ subst ρ B
    ≡⟨ ▸ subst-cong ext B ⟩
      subst σ A |ₛ subst σ B
    ∎
  subst-cong {_} {_} {ρ} {σ} ext (ν[ M ] A) =
    begin
      ν[ M ] subst (Name-v.ext ρ) A
    ≡⟨ ▸ subst-cong (Name-v.ext-cong ext) A ⟩
      ν[ M ] subst (Name-v.ext σ) A
    ∎

  subst-cong-choice ext [] = refl
  subst-cong-choice {_} {_} {ρ} {σ} ext ((f , π , A) ∷ As) =
    begin
      (f , Prefix-v.subst ρ π , subst (Prefix-v.ext π ρ) A) ∷ subst-choice ρ As
    ≡⟨ ▸ subst-cong-choice ext As ⟩
      (f , Prefix-v.subst ρ π , subst (Prefix-v.ext π ρ) A) ∷ subst-choice σ As
    ≡⟨ ▸ Prefix-v.subst-cong ext π ⟩
      (f , Prefix-v.subst σ π , subst (Prefix-v.ext π ρ) A) ∷ subst-choice σ As
    ≡⟨ ▸ subst-cong (Prefix-v.ext-cong π ext) A ⟩
      (f , Prefix-v.subst σ π , subst (Prefix-v.ext π σ) A) ∷ subst-choice σ As
    ∎

  -- | Substituting with the identity function does nothing.
  subst-id : ∀ {Γ} → subst {Γ} id ≗ id
  subst-id-choice : ∀ {Γ} → subst-choice {Γ} id ≗ id
  subst-id Nil = refl
  subst-id (Choice As) = ▸ subst-id-choice As
  subst-id (A |ₛ B) =
    begin
      subst id A |ₛ subst id B
    ≡⟨ Eq.cong₂ _|ₛ_ (subst-id A) (subst-id B) ⟩
      A |ₛ B
    ∎
  subst-id (ν[ M ] A) =
    begin
      ν[ M ] (subst (Name-v.ext id) A)
    ≡⟨ ▸ subst-cong Name-v.ext-id A ⟩
      ν[ M ] (subst id A)
    ≡⟨ ▸ subst-id A ⟩
      ν[ M ] A
    ∎

  subst-id-choice [] = refl
  subst-id-choice {Γ} ((f , π , A) ∷ As) =
    begin
      (f , Prefix-v.subst id π , subst (Prefix-v.ext π id) A) ∷ subst-choice id As
    ≡⟨ ▸ Prefix-v.subst-id π ⟩
      (f , π , subst (Prefix-v.ext π id) A) ∷ subst-choice id As
    ≡⟨ ▸ subst-id-choice As ⟩
      (f , π , subst (Prefix-v.ext π id) A) ∷ As
    ≡⟨ ▸ subst-cong (Prefix-v.ext-id π) A ⟩
      (f , π , subst id A) ∷ As
    ≡⟨ ▸ subst-id A ⟩
      ((f , π , A) ∷ As)
    ∎

  subst-compose : ∀ {Γ Δ η} (ρ : Name Γ → Name Δ) (σ : Name Δ → Name η)
                → (subst σ ∘ subst ρ) ≗ subst (σ ∘ ρ)
  subst-compose-choice : ∀ {Γ Δ η} (ρ : Name Γ → Name Δ) (σ : Name Δ → Name η)
                → (subst-choice σ ∘ subst-choice ρ) ≗ subst-choice (σ ∘ ρ)

  subst-compose {Γ} {Δ} {η} ρ σ Nil = refl
  subst-compose {Γ} {Δ} {η} ρ σ (Choice x) = ▸ subst-compose-choice ρ σ x
  subst-compose {Γ} {Δ} {η} ρ σ (A |ₛ B) =
    begin
      subst σ (subst ρ A) |ₛ subst σ (subst ρ B)
    ≡⟨ ▸ subst-compose ρ σ A ⟩
      subst (σ ∘ ρ) A |ₛ subst σ (subst ρ B)
    ≡⟨ ▸ subst-compose ρ σ B ⟩
      subst (σ ∘ ρ) A |ₛ subst (σ ∘ ρ) B
    ∎
  subst-compose {Γ} {Δ} {η} ρ σ (ν[ M ] A) =
    begin
      ν[ M ] subst (Name-v.ext σ) (subst (Name-v.ext ρ) A)
    ≡⟨ ▸ subst-compose (Name-v.ext ρ) (Name-v.ext σ) A ⟩
      ν[ M ] subst (Name-v.ext σ ∘ Name-v.ext ρ) A
    ≡⟨ ▸ subst-cong (Name-v.ext-compose ρ σ) A ⟩
      ν[ M ] subst (Name-v.ext (σ ∘ ρ)) A
    ∎

  subst-compose-choice {Γ} {Δ} {η} ρ σ [] = refl
  subst-compose-choice {Γ} {Δ} {η} ρ σ ((f , π , A ) ∷ As) =
    begin
      ( f , Prefix-v.subst σ (Prefix-v.subst ρ π) , subst (Prefix-v.ext (Prefix-v.subst ρ π) σ) (subst (Prefix-v.ext π ρ) A) )
      ∷ subst-choice σ (subst-choice ρ As)
    ≡⟨ ▸ Prefix-v.subst-compose ρ σ π ⟩
      ( f , Prefix-v.subst (σ ∘ ρ) π , subst (Prefix-v.ext (Prefix-v.subst ρ π) σ) (subst (Prefix-v.ext π ρ) A) )
      ∷ subst-choice σ (subst-choice ρ As)
    ≡⟨ ▸ Eq.sym (Prefix-v.subst-ext ρ π σ) ⟩
      ( f , Prefix-v.subst (σ ∘ ρ) π , subst (Prefix-v.ext π σ) (subst (Prefix-v.ext π ρ) A) )
      ∷ subst-choice σ (subst-choice ρ As)
    ≡⟨ ▸ subst-compose (Prefix-v.ext π ρ) (Prefix-v.ext π σ) A ⟩
      ( f , Prefix-v.subst (σ ∘ ρ) π , subst (Prefix-v.ext π σ ∘ Prefix-v.ext π ρ) A )
      ∷ subst-choice σ (subst-choice ρ As)
    ≡⟨ ▸ subst-cong (Prefix-v.ext-compose ρ σ π) A ⟩
      (f , Prefix-v.subst (σ ∘ ρ) π , subst (Prefix-v.ext π (σ ∘ ρ)) A )
      ∷ subst-choice σ (subst-choice ρ As)
    ≡⟨ ▸ subst-compose-choice ρ σ As ⟩
      (f , Prefix-v.subst (σ ∘ ρ) π , subst (Prefix-v.ext π (σ ∘ ρ)) A )
      ∷ subst-choice (σ ∘ ρ) As
    ∎
