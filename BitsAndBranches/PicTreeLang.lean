import Mathlib
set_option linter.all false

universe u

/-- Linked Tree. Note: Is there anything specific about HeapTree's here? -/
inductive HeapTree (α : Type u)
| leaf : HeapTree α
| node : HeapTree α → α → HeapTree α → HeapTree α
deriving Repr

namespace HeapTree

/- Checks if the immediate root of a given subtree is ≤ a parent value. If the subtree is a leaf, it's vacuously true.
-/
def RootBounded [LE α] (parentVal : α) : HeapTree α → Prop
| leaf => True
| node l childVal r => childVal ≤ parentVal

/-- ##Defining Max Heap in terms of Prop
-/
inductive IsMaxHeap [LE α] : HeapTree α → Prop where
| leaf : IsMaxHeap leaf
| node (l : HeapTree α) (v : α) (r : HeapTree α) :
    IsMaxHeap l →
    IsMaxHeap r →
    RootBounded v l →
    RootBounded v r →
    IsMaxHeap (node l v r)


def collectNodes [DecidableEq α] : HeapTree α → Finset α
| HeapTree.leaf => {}
| HeapTree.node l v r => (collectNodes l) ∪ {v} ∪ (collectNodes r)


#eval collectNodes (node (node leaf 5 leaf) (2 : ℕ) (node  (leaf) (3 : ℕ) (node (leaf) 4 (leaf))))

def getNode : (HeapTree α) → (Option α)
 | leaf => none
 | node _ v _ => (some v)

/- some lemmas to introduce tactics -/
lemma heap_singleton (v : α) [LE α] :
  IsMaxHeap (HeapTree.node HeapTree.leaf v HeapTree.leaf) := by
  constructor <;> simp[IsMaxHeap.leaf, RootBounded]

 lemma simp_cleanup (a b : Nat) (h1 : a = b) (h2 : b = 3) :
  a = 3 := by
  subst h1
  exact h2

lemma simp_all_cleanup (a b : Nat) (h1 : a = b) (h2 : b = 3) :
  a = 3 := by
  simp_all

/- Back to usual theorems -/

lemma root_is_max (t : HeapTree Nat) (h : IsMaxHeap t) (h_eq : t ≠ leaf) :
  ∀ elem ∈ collectNodes t, (getNode t).get! ≥ elem := by
  induction t with
  | leaf => simp[collectNodes]
  | node l v r ihl ihr =>
     simp[getNode]
     intro elem helem
     unfold collectNodes at helem
     simp at helem
     rcases helem with h1 | h2 | h3
     · simp[h1]
     · cases l with
       | leaf => simp[collectNodes] at h2
       | node l' v' r' =>
          cases h
          case node hl hb hbl hbr =>
          simp[RootBounded] at hb
          have hv': v' ≥ elem := by
           simp[hl] at ihl
           exact (ihl elem h2)
          grind
     · cases r with
       | leaf => simp[collectNodes] at h3
       | node l' v' r' =>
          cases h
          case node hl hb hbl hbr=>
          simp[RootBounded] at hbr
          have hv': v' ≥ elem := by
            simp [hbl] at ihr
            exact (ihr elem h3)
          grind


/-- 2D Grid Position -/
structure Pos where
  x : Int
  y : Int
deriving Repr, DecidableEq

/-- The Visual Tree Structure -/
structure DrawnTree (α : Type u) where
  val   : α
  pos   : Pos
  left  : Option (DrawnTree α)
  right : Option (DrawnTree α)
deriving Repr






/--
  Helper function that threads the current depth and the next available X-coordinate.
  Returns a tuple: (The rendered tree option, The updated next available X)
-/
def layoutAux : HeapTree α → Int → Int → (Option (DrawnTree α) × Int)
| leaf, _, nextX => (none, nextX)
| node l v r, depth, nextX =>

    let (drawLeft, nextX₁) := layoutAux l (depth - 1) nextX

    let rootX := nextX₁

    let (drawRight, nextX₂) := layoutAux r (depth - 1) (rootX + 1)

    let drawnNode := {
      val   := v
      pos   := ⟨rootX, depth⟩
      left  := drawLeft
      right := drawRight
    }
    (some drawnNode, nextX₂)

/--
  Top-level layout function.
  Starts the root at depth 0 and X-coordinate 0.
-/
def layout (t : HeapTree α) : Option (DrawnTree α) :=
  (layoutAux t 0 0).1

#eval (layout (node (leaf) (2: Nat) (node (leaf) (1: Nat) (leaf))))


namespace DrawnTree

/--
  A geometric invariant: Every child must be drawn physically
  lower (smaller Y coordinate) than its parent.
-/

def YDecreases {α : Type u} : DrawnTree α → Prop
| ⟨_, _, none, none⟩ => True
| ⟨_, p, some l, none⟩ => l.pos.y < p.y ∧ YDecreases l
| ⟨_, p, none, some r⟩ => r.pos.y < p.y ∧ YDecreases r
| ⟨_, p, some l, some r⟩ => l.pos.y < p.y ∧ r.pos.y < p.y ∧ YDecreases l ∧ YDecreases r

/-- Lemma 1: layoutAux strictly assigns the given depth to the root's Y-coordinate -/
lemma layoutAux_y_eq_depth {α : Type u} (t : HeapTree α) (depth nextX : Int)
  (dt : DrawnTree α) (nextX' : Int) :
  HeapTree.layoutAux t depth nextX = (some dt, nextX') →
  dt.pos.y = depth := by
  induction t generalizing depth nextX nextX' dt with
  | leaf => simp[layoutAux]
  | node l v r ihl ihr =>
        intro h
        simp [layoutAux] at h
        cases l with
        | leaf => grind
        | node l' v' r' => grind


lemma layout_y_decreases {α : Type u} (t : HeapTree α) (depth nextX : Int)
  (dt : DrawnTree α) (nextX' : Int) :
  HeapTree.layoutAux t depth nextX = (some dt, nextX') →
  DrawnTree.YDecreases dt := by
  induction t generalizing depth nextX dt nextX' with
  | leaf =>
    intro h
    simp [layoutAux] at h
  | node l v r ihl ihr =>
    intro h
    unfold layoutAux at h

    generalize hl : layoutAux l (depth - 1) nextX = resL at h
    rcases resL with ⟨drawLeft, nextX1⟩
    generalize hr : layoutAux r (depth - 1) (nextX1 + 1) = resR at h
    rcases resR with ⟨drawRight, nextX2⟩
    injection h with h_tree h_cursor
    injection h_tree with hdt
    rw[← hdt]
    unfold DrawnTree.YDecreases
    cases h_l : drawLeft with
    | none =>
      cases h_r : drawRight with
      | none => grind
      | some dt_r =>
        have h_r_y := layoutAux_y_eq_depth r (depth - 1) (nextX1 + 1) dt_r nextX2
        have h_r_dec := ihr (depth - 1) (nextX1 + 1) dt_r nextX2
        grind
    | some dt_l =>
      cases h_r : drawRight with
      | none =>
        have h_l_y := layoutAux_y_eq_depth l (depth - 1) nextX dt_l nextX1
        have h_l_dec := ihl (depth - 1) nextX dt_l nextX1
        grind
      | some dt_r =>
        -- Both children exist
        have h_l_y := layoutAux_y_eq_depth l (depth - 1) nextX dt_l nextX1
        have h_l_dec := ihl (depth - 1) nextX dt_l nextX1
        have h_r_y := layoutAux_y_eq_depth r (depth - 1) (nextX1 + 1) dt_r nextX2
        have h_r_dec := ihr (depth - 1) (nextX1 + 1) dt_r nextX2
        grind

theorem layout_x_ordered (t : HeapTree α) (depth : Int) (nextX : Int) :
  match layoutAux t depth nextX with
  | (none, _) => True
  | (some dt, _) =>
      (∀ l, dt.left = some l → l.pos.x < dt.pos.x) ∧
      (∀ r, dt.right = some r → dt.pos.x < r.pos.x) := by
  induction t generalizing nextX depth
  case leaf => simp [layoutAux]
  case node val left right ih_l ih_r =>
    simp [layoutAux]
    generalize h_l : layoutAux val (depth - 1) nextX = res_l
    match res_l with
    | (dt_l, nextX1) =>
      simp
      have prop_l := ih_l (depth - 1) nextX
      rw [h_l] at prop_l

      generalize h_r : layoutAux right (depth - 1) (nextX1 + 1) = res_r
      match res_r with
      | (dt_r, nextX2) =>
        simp
        have prop_r := ih_r (depth - 1) (nextX1 + 1)
        rw [h_r] at prop_r

        constructor
        · intro l h_left; simp [h_left] at *
          sorry
        · intro r h_right; simp [h_right] at *
          sorry



partial def toJson (dt : DrawnTree Nat) : String :=
  let leftStr := match dt.left with
    | none => "null"
    | some l => toJson l
  let rightStr := match dt.right with
    | none => "null"
    | some r => toJson r
  "{\"val\": " ++ toString dt.val ++
  ", \"x\": " ++ toString dt.pos.x ++
  ", \"y\": " ++ toString dt.pos.y ++
  ", \"left\": " ++ leftStr ++
  ", \"right\": " ++ rightStr ++ "}"

end DrawnTree
end HeapTree

def demoTree : HeapTree Nat :=
  HeapTree.node (HeapTree.node (HeapTree.node  HeapTree.leaf 4 HeapTree.leaf) 8 (HeapTree.node HeapTree.leaf 3 HeapTree.leaf)) 15 (HeapTree.node HeapTree.leaf 10 HeapTree.leaf)

def main (args : List String) : IO Unit := do
  match HeapTree.layout demoTree with
  | none => IO.println "null"
  | some drawn => IO.println drawn.toJson
