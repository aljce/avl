open import Relation.Binary using
  (Rel; IsStrictTotalOrder; Tri)
open Tri
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; subst; sym)

open import Level using (_⊔_)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Maybe using (Maybe)
open Maybe

module AVL
  {k r v} (Key : Set k) {_<_ : Rel Key r}
  (is-strict-total-order : IsStrictTotalOrder _≡_ _<_)
  (V : Key -> Set v) where

open import Key Key is-strict-total-order
open IsStrictTotalOrder is-strict-total-order

infix 4 _⊔_↦_

data _⊔_↦_ : ℕ → ℕ → ℕ → Set where
  ↦- : ∀ {n} →     n ⊔ suc n ↦ suc n
  ↦0 : ∀ {n} →     n ⊔ n     ↦ n
  ↦+ : ∀ {n} → suc n ⊔ n     ↦ suc n

data AVL (l-bound r-bound : Bound) : (height : ℕ) -> Set (k ⊔ v ⊔ r) where
  Leaf : l-bound <ᵇ r-bound -> AVL l-bound r-bound 0
  Node :
    ∀ {h-left h-right h}
      (key     : Key)
      (value   : V key)
      (left    : AVL l-bound [ key ] h-left)
      (right   : AVL [ key ] r-bound h-right)
      (balance : h-left ⊔ h-right ↦ h)
    → AVL l-bound r-bound (suc h)


empty : ∀ {l-bound r-bound} -> l-bound <ᵇ r-bound -> AVL l-bound r-bound 0
empty = Leaf

singleton : ∀ {l-bound r-bound} (key : Key) -> V key -> l-bound < key < r-bound -> AVL l-bound r-bound 1
singleton key value bst = Node key value (Leaf (lower bst)) (Leaf (upper bst)) ↦0

lookup : ∀ {h} {l-bound r-bound} -> (key : Key) -> AVL l-bound r-bound h -> Maybe (V key)
lookup key₁ (Leaf _) = nothing
lookup key₁ (Node key₂ value left right balance) with compare key₁ key₂
... | tri< _ _ _ = lookup key₁ left
... | tri≈ _ key₁≡key₂ _ = just (subst V (sym key₁≡key₂) value)
... | tri> _ _ _ = lookup key₁ right

data Insert (l-bound r-bound : Bound) (height : ℕ) : Set (k ⊔ v ⊔ r) where
  +1 : AVL l-bound r-bound (suc height) -> Insert l-bound r-bound height
  +0 : AVL l-bound r-bound height       -> Insert l-bound r-bound height

postulate
  undefined : ∀ {a} {A : Set a} -> A

balance-left : ∀ {h-left h-right h} {l-bound r-bound} (key : Key) -> V key -> Insert l-bound [ key ] h-left -> AVL [ key ] r-bound h-right -> h-left ⊔ h-right ↦ h -> Insert l-bound r-bound (suc h)
balance-left = undefined

balance-right : ∀ {h-left h-right h} {l-bound r-bound} (key : Key) -> V key -> AVL l-bound [ key ] h-left -> Insert [ key ] r-bound h-right -> h-left ⊔ h-right ↦ h -> Insert l-bound r-bound (suc h)
balance-right = undefined

insertWith : ∀ {h} {l-bound r-bound} -> (key : Key) -> V key -> (V key -> V key -> V key) -> l-bound < key < r-bound -> AVL l-bound r-bound h -> Insert l-bound r-bound h
insertWith key₁ value₁ update l-bound<key<r-bound (Leaf l-bound<r-bound) = +1 (singleton key₁ value₁ l-bound<key<r-bound)
insertWith key₁ value₁ update (l-bound<key <×< key<r-bound) (Node key₂ value₂ left right balance) with compare key₁ key₂
... | tri< key₁<key₂ _ _
    = balance-left key₂ value₂ (insertWith key₁ value₁ update (l-bound<key <×< [ key₁<key₂ ]) left) right balance
... | tri≈ _ key₁≡key₂ _ rewrite sym key₁≡key₂
    = +0 (Node key₁ (update value₁ value₂) left right balance)
... | tri> _ _ key₂<key₁ = balance-right key₂ value₂ left (insertWith key₁ value₁ update ([ key₂<key₁ ] <×< key<r-bound) right) balance

