import Mathlib
set_option linter.style.longLine false

universe u

/-We want to construct trees. Some conditions on the trees we want to construct:
 1. Leafs have no labels
 2. Nodes are labelled by natural natural number

A typical tree will look like the following
       3
      / \
     4  lf
    / \
  lf  lf

In order to define or describe the tree, we will use an `algebraic datatype'that will inductively define a tree.

Note that to define a tree, we need two kinds of elements:
1. A leaf is itself a tree
2. A tree can be created by attaching a left tree and a right tree and a labelled value which creates a note

Examples of trees:
1. leaf
2. node leaf 4 leaf
3. node (node leaf 4 leaf) 3 leaf

leaf is a standalone tree, while  one can think of node as a function takes a left tree, a value and right tree to create a tree

-/
inductive mTree
| leaf : mTree
| node : mTree → Nat → mTree → mTree
deriving Repr, DecidableEq
--deriving Repr converts tree datastructure to a string to be displayed on infoview. DecidableEq derives a decision procedure for equality on the type.


/-Above definition means **mTree** object consists of two things: **leaf** and an injective function **node** which returns an objective of the type mTree. mTree is the smallest object that can built from the above.  -/


#check (mTree.node  (mTree.node mTree.leaf 4 mTree.leaf) (3: Nat) (mTree.leaf))
--remove mTree here and see what happens

namespace mTree

#check (node  (node leaf 4 leaf) (3: Nat) (leaf))
--why does mTree need not be added here

/- We define the first function on the tree, which is the mirror function. It reverses a tree. We will do it recursively-/
def mirror : mTree → mTree
 | leaf => leaf
 | node l v r => node (mirror r) v (mirror l)
--guess why we need to write mirror for l and r above


#eval mirror (node  (node leaf 4 leaf) (3: Nat) (leaf))

/-There is a chance we might have messed up something in the definition. Is there? Let's try to check some properties-/
/-First Property: If we take the mirror of a tree and mirror it back, we should get the original tree-/

lemma mirror_of_mirror (t : mTree) : mirror (mirror t) = t := by sorry


/-Seond Property: Mirror is not the identity function, so some element should not mirror back to itself-/
lemma mirror_is_not_id : ∃t, mirror t ≠ t := by
  sorry


/-Third property: Mirror preserves the size of the tree. This needs us to define the size of tree-/
def sizeOfTree : mTree → Nat
 | leaf => 0
 | node l v r => 1 + (sizeOfTree l) + (sizeOfTree r)

#eval sizeOfTree (node  (node leaf 4 leaf) (3: Nat) (leaf))


lemma sizeOfTree_Invariant (t : mTree) : sizeOfTree (mirror t) = sizeOfTree t := by
sorry

--(Hint: Omega)


/-Fourth property, if we flatten the tree into a list, and mirror it, it should be the reverse of the list. This needs us to define a flatten function toList-/
def toList : mTree → List Nat
  | leaf => []
  | node l v r => toList l ++ [v] ++ toList r

theorem toList_mirror (t : mTree) :
  toList (mirror t) = (toList t).reverse := by
  sorry


end mTree
