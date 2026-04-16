import Mathlib

-- WORKSHEET: Functional Programming and Logic in Lean 4
--

inductive MyBool where
| nija : MyBool  -- behaves like "true"
| sullu  : MyBool  -- behaves like "false"
deriving Repr, DecidableEq


-- We define a function by allotting a value to each case.
def negate (p : MyBool) : MyBool :=
  match p with
  | .nija => .sullu
  | .sullu => .nija

-- EVALUATION CHECKS
#eval negate .nija            -- expect: sullu
#eval negate .sullu            -- expect: nija
#eval negate (negate .nija)   -- expect: nija

namespace MyBool

#eval negate nija            -- expect: sullu
#eval negate sullu            -- expect: nija
#eval negate (negate nija)   -- expect: nija


def naive_my_and (p : MyBool) (q : MyBool) : MyBool :=
  match p, q with
  | nija, nija => nija
  | nija, sullu => sullu
  | sullu, nija => sullu
  | sullu, sullu => sullu

#eval naive_my_and nija sullu
#eval naive_my_and nija (naive_my_and nija nija)

-- OPTIMIZATION: Using Wildcards (_)
-- We can simplify this. `my_and` is only true if both inputs are true.
-- For all other cases, it is false.

def shorter_my_and (p : MyBool) (q : MyBool) : MyBool :=
  match p, q with
  | nija, nija => nija
  | _, _ => sullu

-- The `_` is a wildcard that matches "anything else".

-- Even shorter: Pattern match only on `p`.
-- If p is true, the result depends entirely on q.
-- If p is false, the result is always false.
def my_and (p : MyBool) (q : MyBool) : MyBool :=
  match p with
  | nija => q
  | _ => sullu

-- DEFINING OR
-- logic: returns true (nija) if at least one input is true.
def my_or (p : MyBool) (q : MyBool) : MyBool :=
  match p with
  | nija => nija -- If p is true, result is true immediately
  | _ => q           -- If p is false, result depends on q

-- INFIX NOTATION
-- We can assign symbols to these functions.
infix:50 " + " => my_or
infix:51 " * " => my_and   -- Changed from x to * for standard typing

#eval nija + sullu
#eval sullu * nija

--we prove out first theorem, using cases.
example (p : MyBool) (q : MyBool) :
  negate (my_and p q) = my_or (negate p) (negate q) := by
    cases p with
    | nija => simp [negate, my_and, my_or]
    | sullu => simp [negate, my_and, my_or]

/-**Exercises: Prove other DeMorgan Laws**-/
end MyBool

/- We will now define natural numbers: * **sifr**: The end of the chain (Zero).
* **khalifa**: A link that points to the next number (Successor).
-/

inductive MyNat where
| sifr : MyNat
| khalifa : MyNat → MyNat
deriving Repr, DecidableEq

/-
**NOTE** This is not how natural numbers are implemented in Lean for reasons of efficiency of computation, but this is a nice definition to work with, to understand the foundations 'type theoretically'.
-/
namespace MyNat

-- VISUALIZATION:
-- 3 = khalifa (khalifa -(khalifa  sifr))
--

/-
## 2. Recursive Definitions
-/

def my_add (m : MyNat) (n: MyNat) : MyNat :=
match m with
  | sifr => n
  | khalifa k => khalifa (my_add k n)


-- Replace the line below with your eval command
#eval my_add (khalifa sifr)  (khalifa sifr)

/- ## Infix operation -/

infix:50  " +₁ " => my_add

#eval (khalifa sifr +₁ khalifa sifr)

/-
## 3. Proofs of Programs
-/

example : (khalifa sifr +₁ khalifa sifr) = khalifa (khalifa sifr) := by
  rfl

example : ((khalifa (khalifa sifr)) +₁ (khalifa (khalifa sifr))) =
          khalifa (khalifa (khalifa (khalifa sifr))) := by rfl


/-**Induction Prooff**-/

lemma right_id_my_nat (n : MyNat) : (n +₁ sifr) = n := by
  induction n with
  | sifr =>
      -- Base Case: We need to prove `sifr +₁ sifr = sifr`.
      -- This is true by definition of `my_add`.
      rfl
  | khalifa k ih => sorry

end MyNat
