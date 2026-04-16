import Mathlib.Tactic

set_option linter.style.longLine false

/- We will now build a small compiler for a toy language.-/


/-
# A Tiny Imperative Language with a Verified Compiler

This file defines a minimal imperative language and proves several
optimizations correct. We model the language inside Lean and use
theorem proving to show that certain program transformations do not
change the program's behavior.


## Programs in this language

The language contains:
1. variable assignments to natural numbers (mutable)
2. addition and substraction

Here is a simple program written in our language:
`x := 5;`
`y := x + 3;`
`if y then`
`z := 1`
`else`
`z := 0`


But we will use the following representation


`seq`
`  (assign "x" (nat 5))`
`  (seq`
`    (assign "y" (add (var "x") (nat 3)))`
`    (ifThenElse`
`      (var "y")`
`      (assign "z" (nat 1))`
`      (assign "z" (nat 0))))`
## Language Overview

### State
A *state* is a mapping from variable names (strings) to natural numbers.
We represent it as a function `String → Nat`. All variables initially
hold the value `0`. The state is updated when an assignment statement
is executed.

Example expression: `add (var "x") (nat 3)`  -- meaning `x + 3`

### Statements (`Stmt`)
Statements transform the state. They are executed sequentially and may
contain conditional branches.

### What Does Evaluation Mean?

`We define two evaluation functions:`

    `evalExpr (e : Expr) (s : State) : Nat`
    Computes the numeric value of expression `e` in state `s`.

    `evalStmt (stmt : Stmt) (s : State) : State`
    Executes the statement `stmt` starting from state `s` and returns the
    resulting state.

**Evaluation of a program** prog from an initial state (all variables 0)
is simply `evalStmt prog emptyState`. The final state tells us the values
of all variables after the program runs.


-/

-- ==========================================
-- 1. State Definition
-- ==========================================
-- A simple environment mapping variable names to their values
abbrev State := String → Nat

-- The starting state where all variables default to 0
def emptyState : State :=
  fun _ => 0

-- A helper function to mutate the state

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



namespace Expr

#check (nat 3)
#check add (nat 3) (nat 4)
#eval add (nat 3) (nat 4)

--remember what Expr does
-- Evaluates an expression given a current state
def evalExpr (e : Expr) (s : State) : Nat :=
  match e with
  | Expr.nat n   => n
  | Expr.var x   => s x
  | Expr.add a b => evalExpr a s + evalExpr b s
  | Expr.sub a b => evalExpr a s - evalExpr b s

#eval evalExpr (add (nat 3) (nat 4)) emptyState


-- ==========================================
-- 3. Statements (Loop-Free for Guaranteed Termination)
-- ==========================================
inductive Stmt where
  | assign (varName : String) (val : Expr)
  --expresses assignment of `val` to `varName`
  | seq (s1 s2 : Stmt)
  -- expresses sequence of statements s1 and s2, note the recursive nature here
  | ifThenElse (cond : Expr) (thenBranch elseBranch : Stmt)
  -- expresses conditional. Note that cond is defined as a Expr. We will check if the expression evaluates to greated than 0 successively.
  deriving Repr

namespace Stmt

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
-- 4. Verifying Some Properties
-- ==========================================

/-**First Property** : h : h + 1 statement, increases the value of h by 1. -/

lemma inc_h_increases (s : State) :
  (evalStmt (assign "h" (add (var "h") (nat 1))) s) "h" > s "h" := by
  sorry

/-**Second Property** :if the program has the following sequence:
 < some prog block>
  h := h + b
  then the value of h at end of the program is the value of h at the end of < some prog block > + b . -/

lemma seq_increment_add (s : State) (prog : Stmt) (b : Nat) :
  (evalStmt (Stmt.seq prog (Stmt.assign "h" (Expr.add (Expr.var "h") (Expr.nat b)))) s) "h" =
  (evalStmt prog s) "h" + b := by
  sorry

-- ==========================================
-- 5. Some Compiler Optimization Verification
-- ==========================================

-- Constant Folding
lemma add_zero_opt (s : State) (e : Expr) :
  evalExpr (add e (nat 0)) s = evalExpr e s := by
  sorry

-- If the first branch evaluates to zero, it is the same as running a program with second branch
lemma dead_branch_elim (s : State) (s1 s2 : Stmt) :
  evalStmt (ifThenElse (nat 0) s1 s2) s = evalStmt s2 s := by
  sorry

--Program sequencing is associative
lemma seq_assoc (s : State) (s1 s2 s3 : Stmt) :
  evalStmt (seq (seq s1 s2) s3) s =
  evalStmt (seq s1 (seq s2 s3)) s := by
  sorry

-- Shadowing / Overwrite Optimization
lemma overwrite_assign (s : State) (v : Nat) :
  (evalStmt (seq
      (assign "x" (nat 10))
      (assign "x" (nat v))) s) "x" = v := by
  sorry


-- ==========================================
-- 6. Advanced Semantic Optimizations
-- ==========================================

-- Indecisive Branch Merging
lemma branch_merge (s : State) (c : Expr) (stmt : Stmt) :
  evalStmt (ifThenElse c stmt stmt) s = evalStmt stmt s := by
  simp [evalStmt]


-- Expression Saturation (Algebra)
lemma add_sub_cancel_opt (s : State) (e1 e2 : Expr) :
  evalExpr (sub (add e1 e2) e2) s = evalExpr e1 s := by   simp [evalExpr]


-- Instructions with indepdent variables can be reordered Reordering (Alias Analysis)
lemma independent_reorder (s : State) (x y : String) (vx vy : Nat) (h : x ≠ y) :
  evalStmt (seq (assign x (nat vx)) (assign y (nat vy))) s =
  evalStmt (seq (Stmt.assign y (nat vy)) (Stmt.assign x (nat vx))) s := by sorry
  /-**Observe** this requires showing equality of two functions-/
/-  funext k
  simp [evalStmt, evalExpr, update]
  split_ifs <;> aesop
-/
-- Self-Assignment Elimination (The No-Op)
lemma self_assign_noop (s : State) (x : String) :
  evalStmt (Stmt.assign x (Expr.var x)) s = s := by sorry


end Stmt
end Expr
