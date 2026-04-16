import Mathlib

universe u

/-- Linked Tree. Note: Is there anything specific about HeapTree's here? -/
inductive mTree
| leaf : mTree
| node : mTree → Nat → mTree → mTree
deriving Repr, DecidableEq

#check (mTree.node  (mTree.node mTree.leaf 4 mTree.leaf) (3: Nat) (mTree.leaf))

namespace mTree

#check (node  (node leaf 4 leaf) (3: Nat) (leaf))

def mirror : mTree → mTree
 | leaf => leaf
 | node l v r => node (mirror r) v (mirror l)

#eval mirror (node  (node leaf 4 leaf) (3: Nat) (leaf))

lemma mirror_of_mirror (t : mTree) : mirror (mirror t) = t := by sorry


lemma mirror_is_not_id : ∃t, mirror t ≠ t := by
  let t := (node  (node leaf 4 leaf) (3: Nat) (leaf))
  use t
  simp[t, mirror]

def sizeOfTree : mTree → Nat
 | leaf => 0
 | node l _ r => 1 + (sizeOfTree l) + (sizeOfTree r)

#eval sizeOfTree (node  (node leaf 4 leaf) (3: Nat) (leaf))


lemma sizeOfTree_Invariant (t : mTree) : sizeOfTree (mirror t) = sizeOfTree t := by
induction t with
| leaf => simp[mirror]
| node l v r ihl ihr =>
    simp[mirror, sizeOfTree, ihl, ihr]
    omega

def toList : mTree → List Nat
  | leaf => []
  | node l v r => toList l ++ [v] ++ toList r

theorem toList_mirror (t : mTree) :
  toList (mirror t) = (toList t).reverse := by
  sorry


end mTree
