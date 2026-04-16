import Mathlib.Tactic

-- ==========================================
-- 1. State Definition
-- ==========================================
abbrev State := String → Nat

def emptyState : State :=
  fun _ => 0

def update (s : State) (varName : String) (newVal : Nat) : State :=
  fun x => if x = varName then newVal else s x


-- ==========================================
-- 2. Expressions & Statements
-- ==========================================
inductive Expr where
  | nat (n : Nat)
  | var (name : String)
  | add (a b : Expr)
  | sub (a b : Expr)
  deriving Repr

inductive Stmt where
  | assign (varName : String) (val : Expr)
  | seq (s1 s2 : Stmt)
  | ifThenElse (cond : Expr) (thenBranch elseBranch : Stmt)
  deriving Repr


-- ==========================================
-- 3. Custom Monad Definition
-- ==========================================
def MyStateM (s : Type) (α : Type) :=
  s → (α × s)

--explain the instance syntax
instance {s : Type} : Monad (MyStateM s) where
  pure x := fun st => (x, st)
  bind x f := fun st =>
    let (v, st') := x st
    f v st'

/-
type of x : MyStateM (s : String → Nat)  (α)
          : s → (α × s)
type of f : α  → MyState  (s : String → Nat)  (β)
        f : α → s → (β × s)
  x st : (α  × s)
       -> (v, st')
  f v st' : (β × s)


-/

def myGet {s : Type} : MyStateM s s :=
  fun st => (st, st)

-- Note: Changed PUnit to standard Unit
def myModify {s : Type} (f : s → s) : MyStateM s Unit :=
  fun st => ((), f st)

def myRunS {s α : Type} (m : MyStateM s α) (st : s) : s :=
  (m st).2

-- We create an alias specifically for our State type
abbrev MyEvalM (α : Type) := MyStateM State α


-- ==========================================
-- 4. Monadic Evaluators
-- ==========================================
def evalExprM (e : Expr) : MyEvalM Nat := do
  match e with
  | Expr.nat n   => return n
  | Expr.var x   =>
      let s ← myGet
      return s x
  | Expr.add a b =>
      let va ← evalExprM a
      let vb ← evalExprM b
      return va + vb
  | Expr.sub a b =>
      let va ← evalExprM a
      let vb ← evalExprM b
      return va - vb

def evalStmtM (stmt : Stmt) : MyEvalM Unit := do
  match stmt with
  | Stmt.assign varName e =>
      let val ← evalExprM e
      myModify (fun s => update s varName val)

  | Stmt.seq s1 s2 =>
      evalStmtM s1
      evalStmtM s2

  | Stmt.ifThenElse cond s1 s2 =>
      let c ← evalExprM cond
      if c > 0 then
        evalStmtM s1
      else
        evalStmtM s2


-- ==========================================
-- 5. EXECUTION AND PROOFS
-- ==========================================

-- A test program: x = 5; x = x + 10
def testProg : Stmt :=
  Stmt.seq
    (Stmt.assign "x" (Expr.nat 5))
    (Stmt.assign "x" (Expr.add (Expr.var "x") (Expr.nat 10)))

-- Execute the program and read "x"
#eval (myRunS (evalStmtM testProg) emptyState) "x"
-- Expected Output: 15

-- The Theorem: h = h + 1 strictly increases h
lemma gor_monadic (s : State) :
  (myRunS (evalStmtM (Stmt.assign "h" (Expr.add (Expr.var "h") (Expr.nat 1)))) s) "h" > s "h" := by
  simp [evalStmtM, evalExprM, myRunS, bind, pure, myGet, myModify, update]


lemma dead_branch_elim (s : State) (s1 s2 : Stmt) :
  evalStmtM (Stmt.ifThenElse (Expr.nat 0) s1 s2) s = evalStmtM s2 s := by
  simp [evalStmtM, evalExprM, pure, bind]

lemma seq_assoc (s : State) (s1 s2 s3 : Stmt) :
  evalStmtM (Stmt.seq (Stmt.seq s1 s2) s3) s =
  evalStmtM (Stmt.seq s1 (Stmt.seq s2 s3)) s := by
  simp [evalStmtM, bind]
