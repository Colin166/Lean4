import Mathlib

open Real

variable (x y c : ℝ)

/-! Simple goals like these can be solved using `simp?` or `aesop?`. -/
example : deriv (fun _ => c) x = 0 := by simp only [deriv_const']

example : deriv (fun x => x ^ 2) x = 2 * x := by
  simp only [differentiableAt_id', deriv_pow'', Nat.cast_ofNat, Nat.reduceSub, pow_one, deriv_id'',
    mul_one]

example : deriv (fun x => log x) x = 1 / x := by simp only [deriv_log', one_div]

example : deriv (fun x => exp x) x = exp x := by simp only [Real.deriv_exp]

example : deriv (fun x => sin x) x = cos x := by simp only [Real.deriv_sin]

example : deriv (fun x => cos x) x = - sin x := by simp only [deriv_cos']

/-! Complex goals might need some more -/

-- Types are a difficulty here
example : deriv (fun x => x ^ (-1:ℤ)) x = - x ^ (-2:ℤ) := by
  rw [show - x ^ (-2:ℤ) = (-1:ℤ) * x ^ (-2:ℤ) by ring, show (-2 : ℤ) = -1 - 1 by ring]
  apply deriv_zpow (-1:ℤ)

example : deriv (fun x => x ^ (-2:ℤ)) x = (-2:ℤ) * x ^ (-3:ℤ) := by
  rw [show (-3:ℤ) = -2 - 1 by ring]
  apply deriv_zpow (-2:ℤ)

example (hx : x ≠ 0) : deriv (fun x => x ^ (-2 : ℝ)) x = (-2) * x ^ (-3 : ℝ) := by
  rw [show (-3 : ℝ) = -2 - 1 by ring]
  refine Real.deriv_rpow_const (by left; assumption)

example (hx : x ≠ 0) : deriv (fun x => x ^ (-2 / 3 : ℝ)) x = (-2 / 3) * x ^ (-5 / 3 : ℝ) := by
  rw [show (-5 / 3 : ℝ) = - 2 / 3 - 1 by ring]
  refine Real.deriv_rpow_const (by left; assumption)
