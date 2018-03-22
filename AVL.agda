open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Level using (_⊔_)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Maybe using (Maybe; nothing; just)

module AVL
  {k r} (Key : Set k) {_<_ : Rel Key r}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_) where

open IsStrictTotalOrder isStrictTotalOrder

infix 4 _⊔_↦_

data _⊔_↦_ : ℕ → ℕ → ℕ → Set where
  ≡+ : ∀ {n} →     n ⊔ 1 + n ↦ 1 + n
  ≡0 : ∀ {n} →     n ⊔ n     ↦ n
  ≡- : ∀ {n} → 1 + n ⊔ n     ↦ 1 + n

data Tree {v} (V : Key → Set v) : ℕ → Set (k ⊔ v ⊔ r) where
  Empty : Tree V 0
  Leaf :
    ∀ {h-left h-right h}
      (key : Key)
      (value : V key)
      (left : Tree V h-left)
      (right : Tree V h-right)
      (balance : h-left ⊔ h-right ↦ h) → Tree V (suc h)



module _ {v} {V : Key → Set v} where

  empty : Tree V 0
  empty = Empty

  singleton : (key : Key) -> V key -> Tree V 1
  singleton key value = Leaf key value Empty Empty ≡0

  lookup : ∀ {h} (key : Key) -> Tree V h -> Maybe (V key)
  lookup key₁ Empty = nothing
  lookup key₁ (Leaf key₂ value left right balance) with compare key₁ key₂
  ... | tri< _ _ _ = lookup key₁ left
  ... | tri≈ _ key₁≡key₂ _ = {!!} -- just (subst {!!} {!!} {!!})
  ... | tri> _ _ _ = lookup key₁ right
