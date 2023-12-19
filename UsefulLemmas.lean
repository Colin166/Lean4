/-
File : UsefulLemmas.lean
Author : Colin Jones
Date : 10/21/2023
Description : A compilation of useful theorems for working with real numbers
 using Lean 4. Mainly focused for engineers and scientists who would like to
 use Lean 4 for research or derivations. File is split into separate parts
 where each section contains several theorems / lemmas that fit into its
 category.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Perfect

section UsefulTactics
/-!
# Useful Tactics
General
 - have : used to write a intermediate step in the proof
 - calc : produces a calc block that allows user to manipulate expression step-by-step
Rearrangers / solvers
 - ring : used to simplify expressions and complete goals, useful in have statements where you have to rearrange paranthesis
 - field_simp : useful to simplify expressions with division in them
 - norm_num : useful for expressions with numbers
 - simp [*] : a generic tactic that acts like ring
Logical
 - tauto : solves many logical / propositional goals
 - intro : produces a witness for implications or 'for all' / ∀ statements
 - use : produces a subject to prove 'exists' / ∃ statements
 - constructor : takes apart 'and' / ∧ statements in goals and 'iff' / ↔ statements
 - left / right : used when the goal has an 'or' / ∨ statement; switches goal to that direction
 - by_contra : changes proof to a proof by contradiction by assuming that the goal is not true and transforming it into a hypothesis in which the user can use to prove False
 - assumption : sees if the goal matches any hypotheses that the user has, if it does, then it clears the goal
 - apply : more specific form of assumption that takes a hypothesis and applies it to the goal
 - exact : does the same thing as apply but fails if it doesn't solve the goal
-/
example : 2 + 4 = 3 + 3 := by norm_num
example : (P∨Q) → R ↔ (P → R) ∧ (Q → R) := by
  constructor -- breaks apart the iff statement
  intro h -- takes the implication and produces a hypothesis
  constructor -- breaks apart the and statement
  intro p
  have p' : P ∨ Q := by left; assumption -- produces a necessary hypothesis to use in implication
  exact h p'
  intro q
  have q' : P ∨ Q := by right; apply q
  exact h q'
  intro h
  tauto -- makes it easy for logical goals
end UsefulTactics

section Eq_Ne_Symm
/-!
# Equality and Nonequality
Eq.symm : x = y → y = x
Ne.symm : x ≠ y → y ≠ x
-/
variable (x y z : ℝ)
example (h : 2*y = x) : x - 3*y = -y := by
  -- rw [h] does not work because 2*y is not a pattern that lean can recognize
  have h' := by apply Eq.symm h
  rw [h']; ring
example (h : 0 ≠ y) : (x + z)*y = y*(y*x + y*z) / y := by
  have hy : y = (y*1) := by ring
  nth_rw 5 [hy]
  -- have h1 := mul_div_mul_left (y*x + y*z) 1 (h) Statement does
  -- not work because mul_div_mul_left requires a ≠ 0 not 0 ≠ b, so
  have h1 := mul_div_mul_left (y*x + y*z) 1 (Ne.symm h)
  rw [h1]; ring
end Eq_Ne_Symm


section add_sub_theorems
/-!
# Addition and Subtraction Theorems
eq_neg_of_add_eq_zero_right : If a + b = 0 then a = -b
add_right_inj : a + b = a + c iff b = c
-/
end add_sub_theorems


section mul_div_theorems
/-!
# Multiplication and Division Theorems
sq : x^2 = x*x
div_self : If x ≠ 0 then x / x = 1
div_mul_cancel : If y ≠ 0 then x / y * y = x
mul_div_cancel : If y ≠ 0 then x * y / y = x
div_left_inj' : If z ≠ 0 then (x/z = y/z ↔ x = y)
div_mul_eq_div_div_swap : x / (y * z) = x / z / y
div_right_comm : a / b / c = a / c / b
div_div : a / b / c = a / (b * c)
inv_mul_eq_div : a⁻¹ * b = b / a
mul_inv_cancel : If a ≠ 0 then a * a⁻¹ = 1
mul_div_mul_right : If a ≠ 0 then b * a / (c * a) = b / c
-/
variable {x y z : ℝ}
example (hx : x ≠ 0) (hy : y ≥ 0) : 3*x = x*y^(2:ℕ) → y = Real.sqrt 3 := by
  rw [mul_comm x (y^(2:ℕ))]
  intro h
  have h' := by apply mul_right_cancel₀ hx h
  refine ((fun {x y} hx hy => (Real.sqrt_eq_iff_mul_self_eq hx hy).mpr) ?hx hy ?_).symm -- found from apply? tactic which allows you to let the computer figure out what to do
  norm_num; have ysq : y*y = y^2 := by rw [← sq]; norm_num
  rw [ysq]; exact Eq.symm h'
example (hy : y ≠ 0) (hz : z ≠ 0) : (y^2 * z) * x / y / z = x*y := by
  rw [div_div, ← inv_mul_eq_div, mul_assoc, show y^2 = y*y by rw [← sq]; simp [*], mul_inv];
  repeat rw [← mul_assoc]
  have step1 : y⁻¹ * z⁻¹ * y * y * z * x = (y⁻¹ * y) * y * (z⁻¹ * z) * x := by ring
  rw [step1, show y⁻¹ * y = 1 by rw [mul_comm, mul_inv_cancel hy], show z⁻¹ * z = 1 by rw [mul_comm, mul_inv_cancel hz]]
  simp [*]; rw [mul_comm]
example (h : x ≠ 0) : x ^ ((x * y / x) + 1) = x * x ^ y := by
  rw [mul_comm, mul_div_cancel _ h, Real.rpow_add_one h, mul_comm]
end mul_div_theorems


section lemmaless
/-!
# The Lemmaless Statements
These statements do not have a exact lemma that can prove them, but are
common enough to be solved and documented.
-/
example {a b c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) : a / (a * c) = 1 / c := by
  apply eq_one_div_of_mul_eq_one_left; ring; rw [mul_assoc a c a⁻¹, mul_comm c a⁻¹]
  rw [← mul_assoc, mul_inv_cancel ha, mul_assoc, mul_inv_cancel hc, mul_one]
example {a b c : ℝ} (h : c ≠ b - a) : a - b + c ≠ 0 := by
  intro h'
  rw [← add_right_inj (b - a), add_zero] at h'
  have hc : c = (b - a) := by
    rw [← h']
    refine eq_add_of_neg_add_eq ?h
    refine add_right_cancel_iff.mpr ?h.a
    exact neg_sub b a
  contradiction
end lemmaless
