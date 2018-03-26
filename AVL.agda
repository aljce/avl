open import Relation.Binary using
  (Rel; IsStrictTotalOrder; Tri)
open Tri
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; subst; sym)

open import Level using (_⊔_)
open import Data.Nat using (ℕ; pred; _+_)
open ℕ
open import Data.Maybe using (Maybe)
open Maybe
open import Data.Product using (_×_; _,_)

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

max[h-1,h]↦h : ∀ {h} -> max (pred h , h) ↦ h
max[h-1,h]↦h {zero}  = ↦b
max[h-1,h]↦h {suc h} = ↦r

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

singleton
  : ∀ {l-bound r-bound} (key : Key)
   -> V key
   -> l-bound < key < r-bound
   -> AVL l-bound r-bound 1
singleton key value bst = Node key value (Leaf (lower bst)) (Leaf (upper bst)) ↦b

lookup : ∀ {h} {l-bound r-bound} -> (key : Key) -> AVL l-bound r-bound h -> Maybe (V key)
lookup key₁ (Leaf _) = nothing
lookup key₁ (Node key₂ value left right _) with compare key₁ key₂
... | tri< _ _ _ = lookup key₁ left
... | tri≈ _ key₁≡key₂ _ = just (subst V (sym key₁≡key₂) value)
... | tri> _ _ _ = lookup key₁ right

data Insert (l-bound r-bound : Bound) (height : ℕ) : Set (k ⊔ v ⊔ r) where
  +zero : AVL l-bound r-bound height       -> Insert l-bound r-bound height
  +one  : AVL l-bound r-bound (suc height) -> Insert l-bound r-bound height

balance-leftⁱ
  : ∀ {h-left h-right h}
      {l-bound r-bound}
      (key : Key)
    -> V key
    -> Insert l-bound [ key ] h-left
    -> AVL [ key ] r-bound h-right
    -> max (h-left , h-right) ↦ h
    -> Insert l-bound r-bound (suc h)
balance-leftⁱ key₁ value₁ (+zero left₁) right₁ bal = +zero (Node key₁ value₁ left₁ right₁ bal)
balance-leftⁱ key₁ value₁ (+one left) right ↦r = +zero (Node key₁ value₁ left right ↦b)
balance-leftⁱ key₁ value₁ (+one left) right ↦b = +one (Node key₁ value₁ left right ↦l)
balance-leftⁱ key₁ value₁ (+one (Node key₂ value₂ left₂ right₂ ↦l)) right₁ ↦l
  = +zero (Node key₂ value₂ left₂ (Node key₁ value₁ right₂ right₁ ↦b) ↦b)
balance-leftⁱ key₁ value₁ (+one (Node key₂ value₂ left₂ right₂ ↦b)) right₁ ↦l
  = +one (Node key₂ value₂ left₂ (Node key₁ value₁ right₂ right₁ ↦l) ↦r)
balance-leftⁱ key₁ value₁
  (+one (Node key₂ value₂ left₂ (Node key₃ value₃ left₃ right₃ bal) ↦r)) right₁ ↦l
  = +zero (Node key₃ value₃
            (Node key₂ value₂ left₂ left₃ (max[h,l]↦h bal))
            (Node key₁ value₁ right₃ right₁ (max[r,h]↦h bal))
            ↦b)

balance-rightⁱ
  : ∀ {h-left h-right h}
      {l-bound r-bound}
      (key : Key)
    -> V key
    -> AVL l-bound [ key ] h-left
    -> Insert [ key ] r-bound h-right
    -> max (h-left , h-right) ↦ h
    -> Insert l-bound r-bound (suc h)
balance-rightⁱ key₁ value₁ left₁ (+zero right₁) bal = +zero (Node key₁ value₁ left₁ right₁ bal)
balance-rightⁱ key₁ value₁ left₁ (+one right₁) ↦l = +zero (Node key₁ value₁ left₁ right₁ ↦b)
balance-rightⁱ key₁ value₁ left₁ (+one right₁) ↦b = +one (Node key₁ value₁ left₁ right₁ ↦r)
balance-rightⁱ key₁ value₁ left₁ (+one (Node key₂ value₂ left₂ right₂ ↦r)) ↦r
  = +zero (Node key₂ value₂ (Node key₁ value₁ left₁ left₂ ↦b) right₂ ↦b)
balance-rightⁱ key₁ value₁ left₁ (+one (Node key₂ value₂ left₂ right₂ ↦b)) ↦r
  = +one (Node key₂ value₂ (Node key₁ value₁ left₁ left₂ ↦r) right₂ ↦l)
--       1
--      / \
--     /   \
--    L1   2
--        / \
--       /   \
--      3    R2
--     / \
--    /   \
--    L3  R3
balance-rightⁱ key₁ value₁ left₁
  (+one (Node key₂ value₂ (Node key₃ value₃ left₃ right₃ bal) right₂ ↦l)) ↦r
  = +zero (Node key₃ value₃
            (Node key₁ value₁ left₁ left₃ (max[h,l]↦h bal))
            (Node key₂ value₂ right₃ right₂ (max[r,h]↦h bal))
            ↦b)

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
  = +one (singleton key₁ value₁ l-bound<key<r-bound)
insertWith key₁ value₁ update
  (l-bound<key <×< key<r-bound) (Node key₂ value₂ left₁ right₁ bal) with compare key₁ key₂
... | tri< key₁<key₂ _ _
    = balance-leftⁱ key₂ value₂ left₂ right₁ bal
    where left₂ = insertWith key₁ value₁ update (l-bound<key <×< [ key₁<key₂ ]) left₁
... | tri≈ _ key₁≡key₂ _ rewrite sym key₁≡key₂
    = +zero (Node key₁ (update value₁ value₂) left₁ right₁ bal)
... | tri> _ _ key₂<key₁
    = balance-rightⁱ key₂ value₂ left₁ right₂ bal
    where right₂ = insertWith key₁ value₁ update ([ key₂<key₁ ] <×< key<r-bound) right₁

data Delete (l-bound r-bound : Bound) : (height : ℕ) -> Set (k ⊔ v ⊔ r) where
  -zero : ∀ {h} -> AVL l-bound r-bound h -> Delete l-bound r-bound h
  -one  : ∀ {h} -> AVL l-bound r-bound h -> Delete l-bound r-bound (suc h)

delete⇒insert : ∀ {h} {l-bound r-bound} -> Delete l-bound r-bound (suc h) -> Insert l-bound r-bound h
delete⇒insert (-zero avl) = +one avl
delete⇒insert (-one  avl) = +zero avl

insert⇒delete : ∀ {h} {l-bound r-bound} -> Insert l-bound r-bound h -> Delete l-bound r-bound (suc h)
insert⇒delete (+zero avl) = -one avl
insert⇒delete (+one  avl) = -zero avl

balance-leftᵈ
  : ∀ {h-left h-right h}
      {l-bound r-bound}
      (key : Key)
    -> V key
    -> Delete l-bound [ key ] h-left
    -> AVL [ key ] r-bound h-right
    -> max (h-left , h-right) ↦ h
    -> Delete l-bound r-bound (suc h)
balance-leftᵈ {zero} key₁ value₁ (-zero left₁) right₁ bal
  = -zero (Node key₁ value₁ left₁ right₁ bal)
balance-leftᵈ {suc _} key₁ value₁ (-zero left₁) right₁ bal
  = -zero (Node key₁ value₁ left₁ right₁ bal)
balance-leftᵈ {suc _} key₁ value₁ (-one left₁) right₁ ↦l
  = -one (Node key₁ value₁ left₁ right₁ ↦b)
balance-leftᵈ {suc _} key₁ value₁ (-one left₁) right₁ ↦b
  = -zero (Node key₁ value₁ left₁ right₁ ↦r)
balance-leftᵈ {suc _} key₁ value₁ (-one left₁) right₁ ↦r
  = insert⇒delete (balance-rightⁱ key₁ value₁ left₁ (+one right₁) ↦r)

balance-rightᵈ
  : ∀ {h-left h-right h}
      {l-bound r-bound}
      (key : Key)
    -> V key
    -> AVL l-bound [ key ] h-left
    -> Delete [ key ] r-bound h-right
    -> max (h-left , h-right) ↦ h
    -> Delete l-bound r-bound (suc h)
balance-rightᵈ {h-right = zero} key₁ value₁ left₁ (-zero right₁) bal
  = -zero (Node key₁ value₁ left₁ right₁ bal)
balance-rightᵈ {h-right = suc _} key₁ value₁ left₁ (-zero right₁) bal
  = -zero (Node key₁ value₁ left₁ right₁ bal)
balance-rightᵈ {h-right = suc _} key₁ value₁ left₁ (-one right₁) ↦r
  = -one (Node key₁ value₁ left₁ right₁ ↦b)
balance-rightᵈ {h-right = suc _} key₁ value₁ left₁ (-one right₁) ↦b
  = -zero (Node key₁ value₁ left₁ right₁ ↦l)
balance-rightᵈ {h-right = suc _} key₁ value₁ left₁ (-one right₁) ↦l
  = insert⇒delete (balance-leftⁱ key₁ value₁ (+one left₁) right₁ ↦l)

decrease-bound
  : ∀ {h} {l-bound m-bound r-bound}
   -> l-bound <ᵇ m-bound
   -> AVL m-bound r-bound h
   -> AVL l-bound r-bound h
decrease-bound l-bound<m-bound (Leaf m-bound<r-bound)
  = Leaf (<ᵇ-transitive l-bound<m-bound m-bound<r-bound)
decrease-bound l-bound<m-bound (Node key value left right bal)
  = Node key value (decrease-bound l-bound<m-bound left) right bal

increase-bound
  : ∀ {h} {l-bound m-bound r-bound}
  -> m-bound <ᵇ r-bound
  -> AVL l-bound m-bound h
  -> AVL l-bound r-bound h
increase-bound m-bound<r-bound (Leaf l-bound<m-bound)
  = Leaf (<ᵇ-transitive l-bound<m-bound m-bound<r-bound)
increase-bound m-bound<r-bound (Node key value left right bal)
  = Node key value left (increase-bound m-bound<r-bound right) bal

record Minimum (l-bound r-bound : Bound) (height : ℕ) : Set (k ⊔ v ⊔ r) where
  constructor Min
  field
    key         : Key
    value       : V key
    l-bound<key : l-bound <ᵇ [ key ]
    rest        : Insert [ key ] r-bound height

minimum : ∀ {h} {l-bound r-bound} -> AVL l-bound r-bound (suc h) -> Minimum l-bound r-bound h
minimum (Node key₁ value₁ (Leaf l-bound<key₁) right₁ ↦b)
  = Min key₁ value₁ l-bound<key₁ (+zero right₁) 
minimum (Node key₁ value₁ (Leaf l-bound<key₁) right₁ ↦r)
  = Min key₁ value₁ l-bound<key₁ (+zero right₁)
minimum (Node {h-left = suc _} key₁ value₁ left₁ right₁ bal)
  with minimum left₁
... | Min key₂ value₂ l-bound<key₂ rest = Min key₂ value₂ l-bound<key₂ balanced
    where balanced = delete⇒insert (balance-leftᵈ key₁ value₁ (insert⇒delete rest) right₁ bal)

balanceᵈ
   : ∀ {h-left h-right h}
       {l-bound m-bound r-bound}
    -> AVL l-bound m-bound h-left
    -> AVL m-bound r-bound h-right
    -> max (h-left , h-right) ↦ h
    -> Delete l-bound r-bound (suc h)
balanceᵈ left₁ (Leaf m-bound<r-bound) ↦l = -one (increase-bound m-bound<r-bound left₁)
balanceᵈ left₁ (Leaf m-bound<r-bound) ↦b = -one (increase-bound m-bound<r-bound left₁)
balanceᵈ {h-right = suc _} left₁ right₁ bal with minimum right₁
... | Min min-key min-value l-bound<min-key rest
    = balance-rightᵈ min-key min-value (increase-bound l-bound<min-key left₁) (insert⇒delete rest) bal

delete
  : ∀ {h} {l-bound r-bound}
   -> (key : Key)
   -> AVL l-bound r-bound h
   -> Delete l-bound r-bound h
delete key (Leaf l-bound<r-bound) = -zero (Leaf l-bound<r-bound)
delete key (Node key₁ value₁ left₁ right₁ bal) with compare key key₁
... | tri< _ _ _ = balance-leftᵈ key₁ value₁ left₂ right₁ bal
    where left₂  = delete key left₁
... | tri≈ _ _ _ = balanceᵈ left₁ right₁ bal
... | tri> _ _ _ = balance-rightᵈ key₁ value₁ left₁ right₂ bal
    where right₂ = delete key right₁


