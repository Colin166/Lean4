/-
File : FilterEx.lean
Author : Colin Jones
Last Update Date : 04/13/2024
Description : Detailed guide on how to perform a "Filter.Tendsto" proof using the Lean theorem
  prover.
-/

import Mathlib

open Set Filter

variable (a b x : ℝ)

/- ### QUICK NOTES ON SYNTAX ###
-- Set : A set is a collection of distinct objects which for our purposes will be real numbers
-- Set.Ioo : A set that is an open interval e.g. x ∈ Set.Ioo 0 1 ↔ x ∈ (0, 1) ↔ 0 < x < 1
-- Set.Icc : A set that is a closed interval e.g. x ∈ Set.Icc 3 7 ↔ x ∈ [3, 7] ↔ 3 ≤ x ≤ 7
-- Set.Ioi : A set that is an open interval with the right to infinity e.g.
    x ∈ Set.Ioi 0 ↔ x ∈ (0, ∞)
-- Set.Iio : A set that is an open interval with the left to negative infinity e.g.
    x ∈ Set.Iio (-1) ↔ x ∈ (-∞, -1)
-- Filter.Tendsto / Tendsto : Signifies the start of a limit
-- nhds : Stands for neighborhood which is a rigorous way of defining a set of numbers close to a
    number, used for when both sides of the limits exists e.g. x -> a
-- nhdsWithin : Neighborhood around some number within some Set ℝ, used for when only one side of
    the limit exists e.g. x -> a⁺
-- Tendsto.atBot / atBot : Means the limit goes to negative infinity
-- Tendsto.atTop / atTop : Means the limit goes to positive infinity
-/

/- ### NOTES ON PROOFS ### -/
/- General steps for a limit proof :
    1. Manipulate the goal to an easier form
    2. If atBot, change to atTop using "rw [← tendsto_neg_atTop_iff]"
    3. If atTop and the numerator ≠ 1, separate the goals to show that the numerator goes to a
      positive constant and the denominator goes to zero using "Filter.Tendsto.mul_atTop"
    4. If atTop and numerator = 1, change it to show that the denominator goes to zero using
      "refine Filter.Tendsto.inv_tendsto_zero ?_"
    5. If nhdsWithin is in the goal, change it to nhds ⊓ 𝓟 using "rw [nhdsWithin]"
    6. Separate the nhds and the principal using "apply Filter.Tendsto.inf"
    7. Solve the nhds goals individually, splitting up the number in the 2nd nhds accordingly using
      any one of the following theorems
          ⬝ Filter.Tendsto.add
          ⬝ Filter.Tendsto.sub
          ⬝ Filter.Tendsto.mul
    8. Solve the principal goals using the following script
          "refine tendsto_principal_principal.mpr ?h₂.a
          intro x hx
          simp [insert accurate mem_set lemma here] at *"
      List of mem_set lemmas that may be useful are
          ⬝ mem_Ioo
          ⬝ mem_Ioi
          ⬝ mem_Iio
    9. Solve the inequality using previously acquired Lean 4 knowledge
  For some limits there is no easy way to prove their limits. For them it is necessary to prove
  them the old fashion way using "refine Metric.tendsto_nhds_nhds.mpr ?hf.h.a" which sets up an old
  fashioned epsilon-delta proof.
      -/

/- ### EXAMPLE PROOFS ### -/
-- Proof that the limit of x -> 0⁺, f(x) = 1/x = ∞
example : Tendsto (fun x:ℝ => 1/x) (nhdsWithin 0 (Set.Ioo 0 1)) atTop := by
  -- Rewrite 1/x = x⁻¹
  rw [show (fun x:ℝ => 1/x) = (fun x => x⁻¹) by funext; field_simp]
  -- Instead of proving f(x) = 1/x -> ∞, prove (f(x))⁻¹ = x -> 0
  refine Filter.Tendsto.inv_tendsto_zero ?_
  -- Change nhdsWithin into two separate sets: a neighborhood and a principal set
  rw [nhdsWithin]
  -- Separate into two easier goals
  apply Filter.Tendsto.inf
  · -- Simple limits like this (lim x->0, f(x) => x = 0) can be solved using the theorem below
    exact fun ⦃U⦄ a => a
  · -- Theorem below replaces the principal set concept
    refine tendsto_principal_principal.mpr ?h₂.a
    intro x hx
    -- Simpify everywhere to get workable inequalities
    simp [mem_Ioo] at *
    exact hx.1

-- Proof that the limit of x -> a⁺, f(x) = (x - a)⁻¹ = ∞
example : Tendsto (fun x:ℝ => (x - a)⁻¹) (nhdsWithin a (Set.Ioi a)) atTop := by
  refine Filter.Tendsto.inv_tendsto_zero ?_
  rw [nhdsWithin]
  apply Filter.Tendsto.inf
  · -- Separate the zero into a - a for easier proof
    rw [show (0:ℝ) = a - a by rw [sub_self]]
    -- Using limit laws we can break this up into two separate goals showing x -> a and a -> a
    apply Filter.Tendsto.sub
    · -- Simple case
      exact fun ⦃U⦄ a => a
    · -- Constant case
      exact tendsto_const_nhds
  · refine tendsto_principal_principal.mpr ?h₂.a
    intro x hx
    -- Different simpify argument is needed as the set type is different
    simp [mem_Ioi] at *
    assumption

-- Proof that the limit of x -> 1⁺, f(x) = (x² - 1)⁻¹ = ∞
example : Tendsto (fun x:ℝ => (x^(2:ℝ) - 1)⁻¹) (nhdsWithin 1 (Set.Ioo 1 2)) atTop := by
  -- Tactic that allows us to manipulate the function in the original statement
  suffices Tendsto (fun x:ℝ => ((x + 1)*(x - 1))⁻¹) (nhdsWithin 1 (Set.Ioo 1 2)) atTop by
    /- The next three lines are necessary for the "suffices tactic" -/
    apply this.congr'
    rw [eventuallyEq_nhdsWithin_iff]
    filter_upwards with x hx
    /- The above set my new statement and the original statement to be equivalent (which we prove
      the next two lines) -/
    field_simp
    ring
  refine Filter.Tendsto.inv_tendsto_zero ?_
  rw [nhdsWithin]
  apply Filter.Tendsto.inf
  · -- Separate the 0 to make it easier to prove four easier goals
    rw [show (0:ℝ) = (1+1)*(1 - 1) by ring]
    -- Separate the (1 + 1)*(1 - 1) into (1 + 1) and (1 - 1) for two easier goals
    apply Filter.Tendsto.mul
    · apply Filter.Tendsto.add
      · exact fun ⦃U⦄ a => a
      · exact tendsto_const_nhds
    · apply Filter.Tendsto.sub
      · exact fun ⦃U⦄ a => a
      · exact tendsto_const_nhds
  · refine tendsto_principal_principal.mpr ?h₂.a
    intro x hx
    rw [Set.mem_Ioi] at *
    rcases hx with ⟨hx1, hx2⟩
    have h1 : 0 < x + 1 := by linarith
    aesop

-- Proof that lim x -> 1, f(x) = x*(x - 1)⁻¹ = ∞
example : Tendsto (fun x:ℝ => x/(x - 1)) (nhdsWithin 1 (Set.Ioi 1)) atTop := by
  -- Separate the numerator and denominator
  have h : 0 < (1:ℝ) := by positivity
  apply Filter.Tendsto.mul_atTop h
  · -- A slightly more complicated constant case but additional theorems can be found using "apply?"
    exact tendsto_nhdsWithin_of_tendsto_nhds fun ⦃U⦄ a => a
  · refine Filter.Tendsto.inv_tendsto_zero ?_
    rw [nhdsWithin]
    apply Filter.Tendsto.inf
    · rw [show (0:ℝ) = 1 - 1 by linarith]
      apply Filter.Tendsto.sub
      · exact fun ⦃U⦄ a => a
      · exact tendsto_const_nhds
    · refine tendsto_principal_principal.mpr ?h₂.a
      intro x hx
      rw [Set.mem_Ioi] at *
      linarith

-- Proof that lim x -> (1/a)⁻, f(x) = (ax - 1)⁻¹ = -∞
example (hy : 0 < a) : Tendsto (fun x => (a*x - 1)⁻¹) (nhdsWithin (a⁻¹) (Set.Ioo 0 (a⁻¹))) atBot
  := by
    -- When you have an atBot goal it's best to convert it to a atTop goal

    -- Manipulating the function for later
    have h : (fun x => -(a*x - 1)⁻¹) = (fun x => (1 - a*x)⁻¹) := by
      apply funext
      intro x
      field_simp
      refine (div_eq_div_iff_comm (-1) (a * x - 1) 1).mpr ?h.a
      ring
    -- Transform the atBot to atTop
    rw [← tendsto_neg_atTop_iff, h]
    refine Filter.Tendsto.inv_tendsto_zero ?_
    rw [nhdsWithin]
    apply Filter.Tendsto.inf
    · rw [show 0 = 1 - a*a⁻¹ by field_simp]
      apply Filter.Tendsto.sub
      · exact tendsto_const_nhds
      · apply Filter.Tendsto.mul
        · exact tendsto_const_nhds
        · exact fun ⦃U⦄ a => a
    · refine tendsto_principal_principal.mpr ?h₂.a
      intro x hx
      rw [Set.mem_Ioi]
      rcases hx with ⟨hx1, hx2⟩
      have h' : a*x < a*a⁻¹ := by exact (mul_lt_mul_left hy).mpr hx2
      field_simp at h'
      aesop

-- Proof that lim x -> 1⁻, f(x) = x / (x³ - 1) = -∞
-- (Notice how the inequality section is the longest)
example : Tendsto (fun x:ℝ => x / (x^3 - 1)) (nhdsWithin 1 (Set.Iio 1)) atBot := by
  rw [← tendsto_neg_atTop_iff]
  have h : (fun x:ℝ => -(x / (x^3 - 1))) = (fun x:ℝ => x*(-x^3 + 1)⁻¹) := by
    apply funext
    intro x
    rw [mul_comm, ← div_eq_inv_mul, show (-x^3 + 1) = - (x^3 - 1) by ring, div_neg]
  have h' : 0 < (1:ℝ) := by positivity
  rw [h]
  apply Filter.Tendsto.mul_atTop h'
  clear h h'
  · refine tendsto_nhdsWithin_of_tendsto_nhds ?hf.h
    exact fun ⦃U⦄ a => a
  · have h' : (fun x:ℝ => (-x^3 + 1)) = (fun x => ((-x + 1)*(x^2 + x + 1))) := by
      apply funext
      intro x
      ring
    refine Filter.Tendsto.inv_tendsto_zero ?_
    rw [h', show (0:ℝ) = (-1+1)*(1*1 + 1 + 1) by ring]
    rw [nhdsWithin]
    apply Filter.Tendsto.inf
    · apply Filter.Tendsto.mul
      · apply Filter.Tendsto.add
        · exact tendsto_neg 1
        · exact tendsto_const_nhds
      · apply Filter.Tendsto.add
        · apply Filter.Tendsto.add
          · simp_rw [sq]
            apply Filter.Tendsto.mul
            <;> exact fun ⦃U⦄ a => a
          · exact fun ⦃U⦄ a => a
        · exact tendsto_const_nhds
    · refine tendsto_principal_principal.mpr ?h₂.a
      intro x hx
      simp [Set.mem_Ioi] at *
      have h1 : 0 < (-x + 1) := by linarith
      have h2 : 0 < (x^2 + x + 1) := by
        rw [show (x^2 + x + 1) = x*(x + 1) + 1 by ring]
        by_cases hx : -1/2 ≤ x
        · have h' : 0 < x + 1 := by linarith
          have h'' : x + 1 < 2 := by linarith
          have h''' : -x ≤ 1/2 := by linarith
          rw [← neg_lt_iff_pos_add, neg_lt, ← neg_mul, mul_comm]
          calc
            (x + 1) * (-x) ≤ (x + 1)*(1/2) := by gcongr
            _              < 2*(1/2) := by gcongr
            _              = 1 := by ring
        · rw [not_le] at hx
          have h' : x < 0 := by linarith
          by_cases hx : x ≤ -1
          · have h'' : x + 1 ≤ 0 := by linarith
            have h''' : x ≤ 0 := by linarith
            have h'''' : 0 ≤ x*(x+1) := by exact
              mul_nonneg_iff_neg_imp_nonpos.mpr { left := fun a => h'', right := fun a => h''' }
            linarith
          · rw [not_le] at hx
            have h'' : 0 < x + 1 := by linarith
            have h''' : -x < 1 := by linarith
            have h'''' : x + 1 < 1 := by linarith
            rw [← neg_lt_iff_pos_add, neg_lt, ← neg_mul, mul_comm]
            calc
              (x + 1)*(-x) < (x + 1)*(1) := by gcongr
              _            < 1*1 := by rel [h'''']
              _            = 1 := by rw [mul_one]
      aesop
