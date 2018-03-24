open import Relation.Binary using
  (Rel; IsStrictTotalOrder; Tri)
open Tri
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; subst; sym)

open import Level using (_⊔_)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Maybe using (Maybe)
open import Data.Product
open Maybe

module AVL
  {k r v} (Key : Set k) {_<_ : Rel Key r}
  (is-strict-total-order : IsStrictTotalOrder _≡_ _<_)
  (V : Key -> Set v) where

open import Key Key is-strict-total-order
open IsStrictTotalOrder is-strict-total-order

infix 4 max_↦_
data max_↦_ : ℕ × ℕ -> ℕ -> Set where
  ↦l : ∀ {n} → max (suc n , n) ↦ suc n
  ↦b : ∀ {n} → max (n ,     n) ↦ n
  ↦r : ∀ {n} → max (n , suc n) ↦ suc n

max[h,l]↦h : ∀ {l r h} -> max (l , r) ↦ h -> max (h , l) ↦ h
max[h,l]↦h ↦l = ↦b
max[h,l]↦h ↦b = ↦b
max[h,l]↦h ↦r = ↦l

max[r,h]↦h : ∀ {l r h} -> max (l , r) ↦ h -> max (r , h) ↦ h
max[r,h]↦h ↦l = ↦r
max[r,h]↦h ↦b = ↦b
max[r,h]↦h ↦r = ↦b

data AVL (l-bound r-bound : Bound) : (height : ℕ) -> Set (k ⊔ v ⊔ r) where
  Leaf : l-bound <ᵇ r-bound -> AVL l-bound r-bound 0
  Node :
    ∀ {h-left h-right h}
      (key     : Key)
      (value   : V key)
      (left    : AVL l-bound [ key ] h-left)
      (right   : AVL [ key ] r-bound h-right)
      (balance : max (h-left , h-right) ↦ h)
    → AVL l-bound r-bound (suc h)

empty : ∀ {l-bound r-bound} -> l-bound <ᵇ r-bound -> AVL l-bound r-bound 0
empty = Leaf

singleton : ∀ {l-bound r-bound} (key : Key) -> V key -> l-bound < key < r-bound -> AVL l-bound r-bound 1
singleton key value bst = Node key value (Leaf (lower bst)) (Leaf (upper bst)) ↦b

lookup : ∀ {h} {l-bound r-bound} -> (key : Key) -> AVL l-bound r-bound h -> Maybe (V key)
lookup key₁ (Leaf _) = nothing
lookup key₁ (Node key₂ value left right balance) with compare key₁ key₂
... | tri< _ _ _ = lookup key₁ left
... | tri≈ _ key₁≡key₂ _ = just (subst V (sym key₁≡key₂) value)
... | tri> _ _ _ = lookup key₁ right

data Insert (l-bound r-bound : Bound) (height : ℕ) : Set (k ⊔ v ⊔ r) where
  +0 : AVL l-bound r-bound height       -> Insert l-bound r-bound height
  +1 : AVL l-bound r-bound (suc height) -> Insert l-bound r-bound height

postulate
  undefined : ∀ {a} {A : Set a} -> A

balance-leftⁱ
  : ∀ {h-left h-right h}
      {l-bound r-bound}
      (key : Key)
    -> V key
    -> Insert l-bound [ key ] h-left
    -> AVL [ key ] r-bound h-right
    -> max (h-left , h-right) ↦ h
    -> Insert l-bound r-bound (suc h)
balance-leftⁱ key₁ value₁
  (+0 left₁) right₁ balance
  = +0 (Node key₁ value₁ left₁ right₁ balance)
balance-leftⁱ key₁ value₁
  (+1 (Node key₂ value₂ left₂ right₂ ↦l)) right₁ ↦l
  = +0 (Node key₂ value₂ left₂ (Node key₁ value₁ right₂ right₁ ↦b) ↦b)
balance-leftⁱ key₁ value₁
  (+1 (Node key₂ value₂ left₂ right₂ ↦b)) right₁ ↦l
  = +1 (Node key₂ value₂ left₂ (Node key₁ value₁ right₂ right₁ ↦l) ↦r)
balance-leftⁱ key₁ value₁
  (+1 (Node key₂ value₂ left₂ (Node key₃ value₃ left₃ right₃ bal) ↦r)) right₁ ↦l
  = +0 (Node key₃ value₃
         (Node key₂ value₂ left₂ left₃ (max[h,l]↦h bal))
         (Node key₁ value₁ right₃ right₁ (max[r,h]↦h bal))
         ↦b)
balance-leftⁱ key₁ value₁
  (+1 left) right ↦b = +1 (Node key₁ value₁ left right ↦l)
balance-leftⁱ key₁ value₁
  (+1 left) right ↦r = +0 (Node key₁ value₁ left right ↦b)

balance-rightⁱ
  : ∀ {h-left h-right h}
      {l-bound r-bound}
      (key : Key)
    -> V key
    -> AVL l-bound [ key ] h-left
    -> Insert [ key ] r-bound h-right
    -> max (h-left , h-right) ↦ h
    -> Insert l-bound r-bound (suc h)
balance-rightⁱ = undefined

insertWith
  : ∀ {h} {l-bound r-bound}
   -> (key : Key)
   -> V key
   -> (V key -> V key -> V key)
   -> l-bound < key < r-bound
   -> AVL l-bound r-bound h
   -> Insert l-bound r-bound h
insertWith key₁ value₁ update
  l-bound<key<r-bound (Leaf l-bound<r-bound)
  = +1 (singleton key₁ value₁ l-bound<key<r-bound)
insertWith key₁ value₁ update
  (l-bound<key <×< key<r-bound) (Node key₂ value₂ left₁ right₁ balance) with compare key₁ key₂
... | tri< key₁<key₂ _ _
    = balance-leftⁱ key₂ value₂ left₂ right₁ balance
    where left₂ = insertWith key₁ value₁ update (l-bound<key <×< [ key₁<key₂ ]) left₁
... | tri≈ _ key₁≡key₂ _ rewrite sym key₁≡key₂
    = +0 (Node key₁ (update value₁ value₂) left₁ right₁ balance)
... | tri> _ _ key₂<key₁
    = balance-rightⁱ key₂ value₂ left₁ right₂ balance
    where right₂ = insertWith key₁ value₁ update ([ key₂<key₁ ] <×< key<r-bound) right₁

