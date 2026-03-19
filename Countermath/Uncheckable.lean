import Mathlib


/-!
=======================================================================
Uncheckable Statements:

Format:
Each math statement has a Statement, Rationale, and the resoning behind
not being checkable (under UNCHECKABLE).

A proof is given using tactics or otherwise left with sorry.
=======================================================================
-/


section Statement1
/-!
Statement:
If r is rational (r ≠ 0) and x is irrational, then r + x is irrational.

Rationale:
If r and r + x were both rational, then x = (r + x) - r would also be rational,
which contradicts the assumption that x is irrational.

UNCHECKABLE: Involves ℝ and Irrational, which are not decidable/discrete.
  SlimCheck cannot enumerate reals or check Irrational.
  This is a true statement — proof uses: if r + x were rational,
  then x = (r + x) - r would be rational, contradicting hypothesis.
-/

theorem S1 (r : ℚ) (x : ℝ) (hx : Irrational x) : Irrational ((r : ℝ) + x) := by
  -- 1. Proof by contradiction: "Assume (↑r + x) is rational [and we will show a contradiction]."
  intro h_sum_is_rational
  -- 2. Extract the rational 'q' such that ↑r + x = ↑q
  obtain ⟨q, hq⟩ := h_sum_is_rational
  -- 3. Rearrange the equation to isolate 'x': x = ↑q - ↑r
  have hx_eq : x = (q : ℝ) - (r : ℝ) := by
    -- Instead of rw, we use 'linear arithmetic' to move r to the other side
    linarith [hq]
  -- 4. Since the difference of two rationals is rational, x must be rational. We show x = ↑(q - r)
  have x_is_rational : ∃ r_old : ℚ, ↑r_old = x := by
    use (q - r)
    rw [hx_eq]
    push_cast
    rfl
  -- 5. This contradicts our hypothesis 'hx' (that x is irrational).
  exact hx x_is_rational
end Statement1


section Statement2
/-!
Statement:
Prove that there is no rational number whose square is 12.

Rationale:
Suppose m^2 = 12n^2, where m and n have no common factor. It follows that m must be even,
and therefore n must be odd. Let m = 2r. Then we have r^2 = 3n^2, so that r is also odd.
Let r = 2s + 1 and n = 2t + 1. Then 4s^2 + 4s + 1 = 3(4t^2 + 4t + 1) = 12t^2 + 12t + 3,
so that 4(s^2 + s - 3t^2 - 3t) = 2. But this is absurd, since 2 cannot be a multiple of 4.

UNCHECKABLE:
  Missing Instances: The `Rat` type does not have a built-in `SampleableExt`
  or `Shrinkable` instance, which are required for `lspec check` to
  generate random inputs.

  Infinite Domain: Because the set of rational numbers is infinite and
  dense, random sampling (`check`) cannot prove a universal negative,
  and exhaustive testing (`test`) would never terminate.
-/
theorem S2 : ¬ ∃ (q : ℚ), q ^ 2 = 12 := by
  sorry
end Statement2

section Statement15
/-!
Statement:
Prove that no order can be defined in the complex field that turns it
into an ordered field.

Rationale:
By Part (a) of Proposition 1.18, either $i$ or $-i$ must be positive.
Hence $-1=i^2=(-i)^2$ must be positive. But then $1=(-1)^2$, must also
be positive, and this contradicts Part (a) of Proposition 1.18, since 1
and $-1$ cannot both be positive.

UNCHECKABLE:
- **Non-existence Claim**: LSpec tests instances. You cannot sample "all
  possible orders" to prove that none of them work.
- **Abstract Axioms**: Proposition 1.18 refers to the internal logic of
  ordered field axioms, which is a theorem-level proof, not a runtime test.
-/

theorem complex_not_ordered_field : ¬ ∃ (inst : LinearOrder ℂ),
  ∀ (a b c : ℂ), a ≤ b → a + c ≤ b + c := by
  sorry

end Statement15

section Statement930

/-!
Statement:
If a complete topological group $M$ is the countable union $M = \bigcup_{n \geq 1} N_n$
of closed subgroups $N_n$, then at least one $N_n$ is open.

Rationale:
If no $N_n$ is open, then every $N_n$ is nowhere dense. By the Baire Category
Theorem, their countable union would have an empty interior, contradicting
the fact that the union is the entire space $M$.

UNCHECKABLE:
  "Open" and "closed" are non-computable topological properties.
  The infinite union (n ≥ 1) cannot be evaluated by the kernel.
  Baire Category arguments rely on non-constructive existence.
-/


theorem S930 {M : Type*} [TopologicalSpace M] [Group M]
  [IsTopologicalGroup M] [UniformSpace M] [IsUniformGroup M] [CompleteSpace M]
  (N : ℕ → Subgroup M)
  (h_closed : ∀ n, IsClosed (N n : Set M))
  (h_union : (⋃ n, (N n : Set M)) = Set.univ) :
  ∃ n, IsOpen (N n : Set M) := by
  sorry
end Statement930
