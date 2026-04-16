import Mathlib.Tactic

-- ==========================================
-- 1. State Definition
-- ==========================================
-- A simple environment mapping variable names to their values
abbrev State := String → Nat

-- The starting state where all variables default to 0
def emptyState : State :=
  fun _ => 0

-- A helper function to mutate the state
-- Note: Using `=` instead of `==` for standard mathematical equality,
-- which works much better with Lean's `split_ifs` tactic!
def update (s : State) (varName : String) (newVal : Nat) : State :=
  fun x => if x = varName then newVal else s x


-- ==========================================
-- 2. Expressions
-- ==========================================
inductive Expr where
  | nat (n : Nat)
  | var (name : String)
  | add (a b : Expr)
  | sub (a b : Expr)
  deriving Repr

-- Evaluates an expression given a current state
def evalExpr (e : Expr) (s : State) : Nat :=
  match e with
  | Expr.nat n   => n
  | Expr.var x   => s x
  | Expr.add a b => evalExpr a s + evalExpr b s
  | Expr.sub a b => evalExpr a s - evalExpr b s


-- ==========================================
-- 3. Statements (Loop-Free for Guaranteed Termination)
-- ==========================================
inductive Stmt where
  | assign (varName : String) (val : Expr)
  | seq (s1 s2 : Stmt)
  | ifThenElse (cond : Expr) (thenBranch elseBranch : Stmt)
  deriving Repr

def evalStmt (stmt : Stmt) (s : State) : State :=
    match stmt with
    | Stmt.assign varName e =>
        -- MUTATION HAPPENS HERE: We return a brand new state mapping
        let val := evalExpr e s
        update s varName val
    | Stmt.seq s1 s2 =>
        -- Thread the state through s1, then pass the new state to s2
        let s' := evalStmt s1 s
        evalStmt s2 s'
    | Stmt.ifThenElse cond s1 s2 =>
        -- If condition is > 0, we consider it true
        if evalExpr cond s > 0 then
          evalStmt s1 s
        else
          evalStmt s2 s


-- ==========================================
-- 4. Basic Execution Theorems
-- ==========================================

lemma gor (s : State) :
  (evalStmt (Stmt.assign "h" (Expr.add (Expr.var "h") (Expr.nat 1))) s) "h" > s "h" := by
  simp [evalStmt, evalExpr, update]


lemma gory (s : State) (prog : Stmt) (b : Nat) :
  (evalStmt (Stmt.seq prog (Stmt.assign "h" (Expr.add (Expr.var "h") (Expr.nat b)))) s) "h" =
  (evalStmt prog s) "h" + b := by
  simp [evalStmt, update, evalExpr]


-- ==========================================
-- 5. Basic Compiler Optimizations
-- ==========================================

-- Constant Folding
lemma add_zero_opt (s : State) (e : Expr) :
  evalExpr (Expr.add e (Expr.nat 0)) s = evalExpr e s := by
  simp [evalExpr]

-- Dead Branch Elimination
lemma dead_branch_elim (s : State) (s1 s2 : Stmt) :
  evalStmt (Stmt.ifThenElse (Expr.nat 0) s1 s2) s = evalStmt s2 s := by
  simp [evalStmt, evalExpr]

-- AST Flattening (Associativity)
lemma seq_assoc (s : State) (s1 s2 s3 : Stmt) :
  evalStmt (Stmt.seq (Stmt.seq s1 s2) s3) s =
  evalStmt (Stmt.seq s1 (Stmt.seq s2 s3)) s := by
  simp [evalStmt]

-- Shadowing / Overwrite Optimization
lemma overwrite_assign (s : State) (v : Nat) :
  (evalStmt (Stmt.seq (Stmt.assign "x" (Expr.nat 10))
                      (Stmt.assign "x" (Expr.nat v))) s) "x" = v := by
  simp [evalStmt, evalExpr, update]


-- ==========================================
-- 6. Advanced Semantic Optimizations
-- ==========================================

-- Indecisive Branch Merging
lemma branch_merge (s : State) (c : Expr) (stmt : Stmt) :
  evalStmt (Stmt.ifThenElse c stmt stmt) s = evalStmt stmt s := by
  simp [evalStmt]
  -- Lean splits the true/false paths of the if-expression automatically


-- Expression Saturation (Algebra)
lemma add_sub_cancel_opt (s : State) (e1 e2 : Expr) :
  evalExpr (Expr.sub (Expr.add e1 e2) e2) s = evalExpr e1 s := by
  simp [evalExpr]


-- Instruction Reordering (Alias Analysis)
lemma independent_reorder (s : State) (x y : String) (vx vy : Nat) (h : x ≠ y) :
  evalStmt (Stmt.seq (Stmt.assign x (Expr.nat vx)) (Stmt.assign y (Expr.nat vy))) s =
  evalStmt (Stmt.seq (Stmt.assign y (Expr.nat vy)) (Stmt.assign x (Expr.nat vx))) s := by
  -- We must prove the two state functions return the same value for any variable `k`
  funext k
  simp [evalStmt, evalExpr, update]
  -- split_ifs handles all the nested `if k = x` and `if k = y` logic,
  -- and `aesop` automatically discharges the resulting logical contradictions!
  split_ifs <;> aesop

-- Self-Assignment Elimination (The No-Op)
lemma self_assign_noop (s : State) (x : String) :
  evalStmt (Stmt.assign x (Expr.var x)) s = s := by
  funext k
  simp only [evalStmt, evalExpr, update, ite_eq_right_iff]
  intro hk
  simp[hk]
