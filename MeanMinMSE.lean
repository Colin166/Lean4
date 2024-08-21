import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum

open Nat

open Finset

open BigOperators

variable (Y : ℕ → ℝ) (Yhat : ℝ)
noncomputable def Ymean (n : ℕ) : ℝ := (∑ i in range n, Y i) / n
noncomputable def SSE (n : ℕ) (Yhat : ℝ) : ℝ := ∑ i in range n, (Y i - Yhat)^(2:ℕ)
noncomputable def MSE (n : ℕ) (Yhat : ℝ) : ℝ := SSE Y n Yhat / n

theorem SumOfElementSubMeanEqZero (n : ℕ) (Y : ℕ → ℝ) (hn : 0 < n) : ∑ i in range n, (Y i - Ymean Y n) = 0 := by
  simp [sum_add_distrib]; dsimp [Ymean]; field_simp; rw [mul_comm, sub_self]

theorem SSE_Rewrite (n : ℕ) (Yhat : ℝ) (Y : ℕ → ℝ) (hn : 0 < n)  : SSE Y n Yhat = n*(Ymean Y n - Yhat)^2 + ∑ i in range n, ((Y i - Ymean Y n)^2) := by
  dsimp [SSE];
  have h1 : ∑ i in range n, ((Ymean Y n - Yhat)^2) = n*(Ymean Y n - Yhat)^2 := by
    have ConsSum {x : ℝ} : ∑ i in range n, x = n*x := by
      refine sum_range_induction (fun k => x) (fun n => ↑n * x) ?base ?step n
      simp [*]; intro n; simp [*]; ring
    apply ConsSum
  have h2 : ∑ i in range n, (2*(Y i - Ymean Y n)*(Ymean Y n - Yhat)) = (2*(Ymean Y n - Yhat))*(∑ i in range n, (Y i - Ymean Y n)) := by
    repeat rw [mul_sum]; refine (sum_eq_sum_iff_of_le ?h).mpr ?_ <;> {intro i hi; linarith}
  calc
    ∑ i in range n, (Y i - Yhat) ^ 2 = ∑ i in range n, ((Y i - Ymean Y n) + (Ymean Y n - Yhat)) ^ 2 := by simp [*]
    _ = ∑ i in range n, ((Y i - Ymean Y n)^2 + 2*(Y i - Ymean Y n)*(Ymean Y n - Yhat) + (Ymean Y n - Yhat)^2) := by refine (sum_congr rfl ?_).symm; intro x hx; exact Eq.symm (add_sq (Y x - Ymean Y n) (Ymean Y n - Yhat))
    _ = ∑ i in range n, ((Y i - Ymean Y n)^2) + ∑ i in range n, 2*(Y i - Ymean Y n)*(Ymean Y n - Yhat) + ∑ i in range n, ((Ymean Y n - Yhat)^2) := by simp [sum_add_distrib]
    _ = ∑ i in range n, ((Y i - Ymean Y n)^2) + ∑ i in range n, 2*(Y i - Ymean Y n)*(Ymean Y n - Yhat) + n*(Ymean Y n - Yhat)^2 := by rw [h1]
    _ = n*(Ymean Y n - Yhat)^2 + ∑ i in range n, ((Y i - Ymean Y n)^2) + ∑ i in range n, 2*(Y i - Ymean Y n)*(Ymean Y n - Yhat) := by ring
    _ = n*(Ymean Y n - Yhat)^2 + ∑ i in range n, ((Y i - Ymean Y n)^2) := by rw [h2, SumOfElementSubMeanEqZero n Y hn, mul_zero, add_zero]

theorem SSEEqMinAtMeanEst (n : ℕ) (Y : ℕ → ℝ) (hn : 0 < n) : Yhat = Ymean Y n → SSE Y n Yhat = ∑ i in range n, ((Y i - Ymean Y n)^2) := by
  intro h; rw [SSE_Rewrite n Yhat Y hn, h]; field_simp

theorem SSEGtMinNotMeanEst (n : ℕ) (Y : ℕ → ℝ) (hn : 0 < n) : Yhat ≠ Ymean Y n → SSE Y n Yhat > ∑ i in range n, ((Y i - Ymean Y n)^2) := by
  intro h; rw [SSE_Rewrite n Yhat Y hn]; have g := by exact Ne.lt_or_lt h
  have RealnGtZero : 0 < (n:ℝ) := by simp [*]
  rcases g with h1 | h2
  <;> {
  first | have SubGtZero : (Ymean Y n - Yhat) > 0 := by exact sub_pos.mpr h1 | have SubLtZero : (Ymean Y n - Yhat) < 0 := by exact sub_neg.mpr h2
  have SubGtZero' : (Ymean Y n - Yhat)^2 > 0 := by first | exact sq_pos_of_pos SubGtZero | exact sq_pos_of_neg SubLtZero
  have SubGtZero'' : n * (Ymean Y n - Yhat)^2 > 0 := by refine Real.mul_pos ?_ SubGtZero'; assumption
  linarith }

theorem MSE_EqMinAtMeanEst (n : ℕ) (Y : ℕ → ℝ) (hn : 0 < n) : Yhat = Ymean Y n → MSE Y n Yhat = (∑ i in range n, ((Y i - Ymean Y n)^2)) / n := by
  intro h; dsimp [MSE]; rw [SSEEqMinAtMeanEst Yhat n Y hn h];

theorem MSEGtMinNotMeanEst  (n : ℕ) (Y : ℕ → ℝ) (hn : 0 < n) : Yhat ≠ Ymean Y n → MSE Y n Yhat > (∑ i in range n, ((Y i - Ymean Y n)^2)) / n := by
  intro h; dsimp [MSE]; rw [← inv_mul_eq_div, ← inv_mul_eq_div]; rel [SSEGtMinNotMeanEst Yhat n Y hn h]

theorem MinMSE_Zero (n : ℕ) (Y : ℕ → ℝ) (hn : 0 < n) (hm : m ≠ Ymean Y n) : min (MSE Y n (Ymean Y n)) (MSE Y n m) = MSE Y n (Ymean Y n) := by
  dsimp [min]; simp [*];
  have h1 := by apply MSEGtMinNotMeanEst m n Y hn hm
  have h2 := by apply MSE_EqMinAtMeanEst (Ymean Y n) n Y hn rfl
  linarith
