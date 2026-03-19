import Mathlib
import LSpec

open LSpec

/-!
=======================================================================
# Countermath.lean

This file stores statements checkable by SlimCheck or LSpec's built-in
exhaustion for bounded quantification.

Checkable statements involve decidable propositions over discrete types
(Naturals, Integers, Bool, etc.).

Uncheckable statements (e.g., involving Real numbers or non-decidable
properties) are stored in `Uncheckable.lean`.
=======================================================================
-/



/-!
=======================================================================
Examples of how lspec works:

Note: <| is preferred over $ for composing tests into sequences
=======================================================================
-/

section Examples

-- 1. Simple Unit Test
#lspec test "Nat inequality" (4 ≠ 5)
-- ✓ ∃: Nat inequality

-- 2. Composed Unit Tests
-- Fixed the implicit argument error by annotating the empty list type
#lspec test "Boolean logic" (true && true) <|
  test "List length check" ([1, 2, 3].length = 3) <|
  test "List emptiness" (¬ ([] : List Nat).length > 0)
-- ✓ ∃: Boolean logic
-- ✓ ∃: List length check
-- ✓ ∃: List emptiness


-- 3. Bounded Universal Quantification
-- LSpec automatically iterates through small ranges of Nats (0-100)
-- to verify properties without requiring the full SlimCheck engine.
#lspec test "Small Nat addition" <| ∀ n, n < 10 → n + 5 < 16
-- ✓ ∃: Small Nat addition


#lspec
  test "rational addition" ((1/2 : Rat) + (1/3 : Rat) = 5/6) <|
  test "rational inequality" ((1/3 : Rat) ≠ 0.33)
-- ✓ ∃: rational addition
-- ✓ ∃: rational inequality

end Examples



/-!
=======================================================================
Checkable Statements:
=======================================================================
-/

section Statement23
/-!
Statement:
Give an example of a nonempty subset $U$ of $\mathbf{R}^2$ such that $U$ is
closed under scalar multiplication, but $U$ is not a subspace of $\mathbf{R}^2$.

Rationale:
$U = \{(x, y) \in \mathbf{R}^2 : |x|=|y|\}$. For $(x, y) \in U$ and $\lambda \in \mathbb{R}$,
it follows $\lambda(x, y) = (\lambda x, \lambda y)$, so $|\lambda x| = |\lambda||x| = |\lambda||y| = |\lambda y|$.
Therefore, $\lambda(x, y) \in U$. On the other hand, consider $a=(1,-1), b=(1,1) \in U$.
Then, $a+b=(1,-1)+(1,1)=(2,0) \notin U$. So, $U$ is not a subspace of $\mathbf{R}^2$.

CHECKABLE:
LSpec can verify the counterexample $(1,-1) + (1,1) = (2,0)$ and confirm
that $(2,0)$ does not satisfy the condition $|x| = |y|$.
-/

-- Define the condition for being in the set U
-- Takes a pair of integers, and returns True if |p.1| == |p.2|
def inU (p : Int × Int) : Bool :=
  p.1.natAbs == p.2.natAbs

#lspec test "S23: Counterexample: Sum of elements in U is not in U" (
  let a := (1, -1)
  let b := (1, 1)
  let sum := (a.1 + b.1, a.2 + b.2) -- (2, 0)
  -- 'a' and 'b' are in U, but their sum is not
  inU a && inU b && !inU sum
)
-- ✓ ∃: S23: Counterexample: Sum of elements in U is not in U

end Statement23


section Statement24
/-!
Statement:
"Prove that the union of two subspaces of $V$ is a subspace of $V$ if and
only if one of the subspaces is contained in the other."

Rationale:
To prove this one way, suppose for purposes of contradiction that for $U_1$ and
$U_2$, which are subspaces of $V$, that $U_1 \cup U_2$ is a subspace and neither
is completely contained within the other. In other words, $U_1 \nsubseteq U_2$
and $U_2 \nsubseteq U_1$. We will show that you can pick a vector $v \in U_1$
and a vector $u \in U_2$ such that $v+u \notin U_1 \cup U_2$, proving that
if $U_1 \cup U_2$ is a subspace, one must be completely contained inside the other.

If $U_1 \nsubseteq U_2$, we can pick a $v \in U_1$ such that $v \notin U_2$.
If $U_2 \nsubseteq U_1$, then we can pick a $u \in U_2$ such that $u \notin U_1$.
If $v+u \in U_1 \cup U_2$, then $v+u$ must be in $U_1$ or $U_2$. But:
- $v+u \in U_1 \Rightarrow v+u+(-v) \in U_1 \Rightarrow u \in U_1$
- $v+u \in U_2 \Rightarrow v+u+(-u) \in U_2 \Rightarrow v \in U_2$

This is a contradiction, as each element was defined to not be in these subspaces.
Thus our initial assumption must have been wrong, and $U_1 \subseteq U_2$ or
$U_2 \subseteq U_1$. To prove the other way, let $U_1 \subseteq U_2$ (WLOG).
Then $U_1 \cup U_2 = U_2$. Since $U_2$ is a subspace, the union is as well.


CHECKABLE:
LSpec can verify the logic of the counterexample by testing specific subspaces
(like the axes of a plane) that are not contained in one another.

We verify the counterexample from the rationale.
Let U1 be the X-axis and U2 be the Y-axis. Neither is contained in the
other. We check that while (1,0) and (0,1) are in the union, their sum
(1,1) is not.
-/

-- Define two subspaces such that neither is contained in the other
-- Use 'Bool' and '==' instead of 'Prop' and '='
def onXAxis (p : Int × Int) : Bool := p.2 == 0
def onYAxis (p : Int × Int) : Bool := p.1 == 0

#lspec test "S24: Union of axes is not closed under addition" (
  let u1 := (1, 0)
  let u2 := (0, 1)
  let sum := (u1.1 + u2.1, u1.2 + u2.2)
  -- Use Boolean operators: && (and), || (or), ! (not)
  -- We essentially ask three questions:
      -- Is u1 (1,0) in the union of the two subspaces? (True)
      -- Is u2 (0,1) in the union of the two subspaces? (True)
      -- Is u1 + u2 (1,1) NOT in the union of the two subspaces? (True)
  (onXAxis u1 || onYAxis u1) &&
  (onXAxis u2 || onYAxis u2) &&
  !(onXAxis sum || onYAxis sum)
)
-- ✓ ∃: S24: Union of axes is not closed under addition

end Statement24


section Statement36
/-!
Statement:
The polynomial $x^2 - \sqrt{2}$ is irreducible over $\mathbb{Z}[\sqrt{2}]$.

Rationale:
If $x^2 - \sqrt{2}$ were reducible, it would have a root $a + b\sqrt{2}$ where
$a, b \in \mathbb{Z}$.
Plugging this root into the polynomial gives:
$(a + b\sqrt{2})^2 - \sqrt{2} = 0$
$a^2 + 2b^2 + (2ab - 1)\sqrt{2} = 0$
For this to hold, the coefficient $(2ab - 1)$ must be $0$, meaning $2ab = 1$.

CHECKABLE:
LSpec can use SlimCheck to sample integers $a$ and $b$ to verify that $2ab$ is never $1$.
-/

#lspec check "S36: Rationale contradiction: 2ab is never 1 for integers" <|
  ∀ (a b : Int), 2 * a * b != 1
-- ✓ ∃: S36: Rationale contradiction: 2ab is never 1 for integers

end Statement36


section Statement155
/-!
Statement:
Two initial segments of natural numbers N_m and N_n are equivalent
if and only if m = n.

Rationale:
The rationale uses induction to prove that if two initial segments
are equivalent, their predecessors must also be equivalent,
leading to a contradiction if the sizes differ.

CHECKABLE:
LSpec can verify the truth of this equivalence by comparing
the sizes of the sets.
-/

-- 1. Test specific cases (m = n and m ≠ n)
#lspec test "S155: Equivalent segments (5, 5)" (
  let m := 5
  let n := 5
  (m == n) == (Fintype.card (Fin m) == Fintype.card (Fin n))
)
-- ✓ ∃: S155: Equivalent segments (5, 5)

#lspec test "S155: Non-equivalent segments (3, 7)" (
  let m := 3
  let n := 7
  (m == n) == (Fintype.card (Fin m) == Fintype.card (Fin n))
)
-- ✓ ∃: S155: Non-equivalent segments (3, 7)


-- 2. Use 'check' to verify the logic for random pairs
#lspec check "S155: General equivalence for natural numbers" <|
  ∀ (m n : Nat), (m == n) ↔ (Fintype.card (Fin m) == Fintype.card (Fin n))
-- ✓ ∃: S155: General equivalence for natural numbers

end Statement155


section Statement249
/-!
Statement:
Let $A$ be a $*$-algebra and $A'$ be its Cayley-Dickson construction.
Then $A'$ is not a real algebra.

Rationale:
A real algebra is defined by the property that conjugation is the identity
($a^* = a$). In the Cayley-Dickson construction, the conjugate of an
element $(x, y)$ is $(x^*, -y)$. For $(x, y) = (x^*, -y)$ to hold, $y$
must be $0$. Since a $*$-algebra is a unitary division algebra, it
contains a non-zero identity element ($1 \neq 0$), allowing us to
construct elements where $y \neq 0$.

CHECKABLE:
LSpec can verify this by checking if the conjugation function
is the identity function.
-/

-- Cayley-Dickson conjugation: (x, y)* = (x*, -y)
-- We use 'Int' because 'Float' lacks a built-in 'SampleableExt' instance.
def cd_conj (z : Int × Int) : Int × Int :=
  (z.1, -z.2)

#lspec check "S249: Cayley-Dickson construction is not a real algebra" <|
  ∀ (z : Int × Int), z == cd_conj z

-- × ∃: S249: Cayley-Dickson construction is not a real algebra
--
-- ===================
-- Found problems!
-- z := (0, 1)
-- issue: false does not hold
-- (1 shrinks)
-- -------------------

end Statement249


section Statement259
/-!
Statement:
For any elements a, b in a semigroup and positive integers m,n
If a ∘ b = b ∘ a, then a^m ∘ b^n = b^n ∘ a^m
This is not always the case that a ∘ b = b ∘ a, and I will show such a case.

If two elements commute, their powers commute. However, if powers commute,
it does not imply the base elements commute.

Rationale:
In any semigroup, $a \circ b = b \circ a \implies a^m \circ b^n = b^n \circ a^m$.
To show the converse is false, consider the Dihedral group $D_3$.
Let $a$ be a rotation of $120^\circ$ ($a^3 = e$) and $b$ be a reflection ($b^2 = e$).
Then $a^3 \circ b^2 = e \circ e = e$ and $b^2 \circ a^3 = e \circ e = e$.
The powers commute, but $a \circ b \neq b \circ a$.

CHECKABLE:
LSpec will compute the actual values of the matrix multiplications.
Because matrix multiplication is decidable for fixed-size matrices over
integers, Lean can reduce the expressions to their resulting matrices
and compare them directly.
-/

-- Define the 2x2 matrices using a simple row-based constructor !![a, b; c, d]
def A : Matrix (Fin 2) (Fin 2) Int := !![1, 0; 0, 0]
def B : Matrix (Fin 2) (Fin 2) Int := !![0, 0; 1, 0]

#lspec test "S259: Matrix counterexample: A^2 * B^2 = B^2 * A^2 but AB != BA" (
  let m := 2
  let n := 2
  let A2 := A ^ m
  let B2 := B ^ n

  -- 1. Check if powers commute (Both should be the zero matrix)
  (A2 * B2 == B2 * A2) &&
  -- 2. Check that the original matrices do NOT commute (AB = 0, BA = B)
  !(A * B == B * A)
)
-- ✓ ∃: S259: Matrix counterexample: A^2 * B^2 = B^2 * A^2 but AB != BA

end Statement259
