module Test where

open import Data.Product using (_,_)
open import Data.List using (_∷_; [])
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Non-Dependent where
  open import Function using (const)
  open import Data.String using (String)
  open import Data.Nat using (ℕ)
  open import Data.Nat.Properties using (<-isStrictTotalOrder)
  open import Tree ℕ <-isStrictTotalOrder (const String)

  test-tree₁ : Tree
  test-tree₁ = fromList ((1 , "foo") ∷ (2 , "bar") ∷ (3 , "baz") ∷ [])

  lookup-unit₁ : lookup 3 test-tree₁ ≡ just "baz"
  lookup-unit₁ = refl

  lookup-unit₂ : lookup 4 test-tree₁ ≡ nothing
  lookup-unit₂ = refl

  test-tree₂ : Tree
  test-tree₂ = delete 3 test-tree₁

  lookup-unit₃ : lookup 3 test-tree₂ ≡ nothing
  lookup-unit₃ = refl

module Dependent where
  open import Data.Vec using (Vec)
  open Vec
  open import Data.String using (String)
  open import Data.Nat using (ℕ)
  open import Data.Nat.Properties using (<-isStrictTotalOrder)
  open import Tree ℕ <-isStrictTotalOrder (Vec String)

  test-tree₁ : Tree
  test-tree₁ = fromList ((0 , []) ∷ (1 , "foo" ∷ []) ∷ (2 , "bar" ∷ "quix" ∷ []) ∷ [])

  lookup-unit₁ : lookup 2 test-tree₁ ≡ just ("bar" ∷ "quix" ∷ [])
  lookup-unit₁ = refl

  lookup-unit₂ : lookup 4 test-tree₁ ≡ nothing
  lookup-unit₂ = refl

  test-tree₂ : Tree
  test-tree₂ = delete 3 test-tree₁

  lookup-unit₃ : lookup 3 test-tree₂ ≡ nothing
  lookup-unit₃ = refl



