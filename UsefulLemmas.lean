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
example (h : x ≠ 0) (hy : y ≥ 0) : 2*x = x*y^2 → y = Real.sqrt 2 := by
  intro h1
  rw [mul_comm x, ← div_left_inj' h, mul_div_assoc, mul_div_assoc] at h1
  rw [show x/x = 1 by apply div_self h, mul_one, mul_one] at h1
  have h1' := by apply Eq.symm h1
  have h2 : 2 = ((2:ℝ) ^ ((1:ℝ)/(2:ℝ) * 2)) := by norm_num
  rw [Real.sqrt_eq_rpow]; nth_rw 1 [h2, h1]; norm_num
  apply Eq.symm
  have step1 :=
    calc
      (y ^ 2) ^ (1 / 2) = y ^ (2 * (1/2)) := by rw [← Real.rpow_mul hy]
      _ = y := by norm_num
  have twoeqtwo : (2:ℝ) = (2:ℕ) := by rfl
  nth_rw 1 [twoeqtwo]



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
