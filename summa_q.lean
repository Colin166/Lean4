import Mathlib

open BigOperators Filter Finset Nat Set

variable (n m : ℕ) (w u : ℤ) (p q : ℚ) (y z : ℝ) (a b : α) (X Y Yhat f f1 f2 : ℕ → ℚ)

-------------------------------------------------------------------
/- ### Testing Functions ### -/

-- ID Function : Spits back the same number
def id_func := (n : ℚ)

-- AddOne Function : Adds one to the number
def summa_add_one := (n + 1 : ℚ)

-- TestList : Example of a list of rational numbers
def test_list
  | 0 => (15 / 4 : ℚ)
  | 1 => (13 / 4)
  | 2 => (11 / 4)
  | 3 => (9 / 4)
  | 4 => (23 / 10)
  | _ => 0

def toupt
  | 0 => fun (x:ℕ) => id_func x
  | 1 => fun (x:ℕ) => summa_add_one x
  | 2 => fun (x:ℕ) => test_list x
  | _ => fun _ => (0:ℚ)

def qoutp (p q : ℚ) := fun (x : ℕ) => p * x + q

-------------------------------------------------------------------
/- ### Stat Functions ### -/

def mean := (1 / n : ℚ) * ∑ i in range n, Y i
#eval mean 8 (fun (x:ℕ) => x^2)

def SSE := ∑ i in range n, (Y i - Yhat i) ^ 2
#eval SSE 5 (fun _ => 1) (fun x => factorial x)
#eval SSE 4 test_list (fun _ => mean 4 test_list)

def MSE := (1 / n : ℚ) * SSE n Y Yhat
#eval MSE 5 test_list summa_add_one

def SSE_lin := (fun (p q : ℚ) => SSE n Y (fun (i : ℕ) => p * X i + q))
#check SSE_lin
#eval SSE_lin 4 1 test_list 3 2

-------------------------------------------------------------------
/- ### Proofs ### -/

theorem self_func_sse : SSE n f f = 0 := by
  have h : 2 ≠ 0 := by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  simp_rw [SSE, sub_self, zero_pow h, sum_const_zero]

theorem self_func_mse : MSE n f f = 0 := by rw [MSE, self_func_sse, mul_zero]

theorem mean_prod (hn : 0 < n) : (n : ℚ) * mean n Y = ∑ i in range n, Y i := by
  have h : (n : ℚ) / n = 1 := div_self (_root_.ne_of_gt (cast_pos.mpr hn))
  rw [mean, show 1 / ↑n * ∑ i in range n, Y i = (∑ i in range n, Y i) / n by ring]
  rw [mul_div_left_comm, h, mul_one]

theorem sum_deviations_sub_mean_zero (hn : 0 < (n:ℚ)) : ∑ i in range n, (Y i - mean n Y) = 0 := by
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mean, mul_sum, mul_sum, sub_eq_add_neg,
    ← neg_one_mul, mul_sum, ← sum_add_distrib, show 0 = ∑ i in range n, (0 : ℚ) by
    rw [sum_const_zero]]
  congr with x
  ring_nf!
  field_simp

theorem sse_rw_yhat_cons (h : ∀ i, Yhat i = p) : SSE n Y Yhat = ∑ i in range n, (Y i - mean n Y) ^
  2 + 2 * (mean n Y - p) * ∑ i in range n, (Y i - mean n Y) + n * (mean n Y - p) ^ 2 := by
    rw [show n * (mean n Y - p) ^ 2 = ∑ i in range n, (mean n Y - p) ^ 2 by simp only [sum_const,
      card_range, nsmul_eq_mul], mul_sum, add_comm, ← sum_add_distrib, ← sum_add_distrib, SSE]
    congr with x
    rw [show Y x - Yhat x = (Y x - mean n Y) + (mean n Y - Yhat x) by rw [sub_add_sub_cancel], h]
    ring

theorem sse_rw_yhat_cons' : SSE n Y (fun _ => p) = ∑ i in range n, (Y i - mean n Y) ^
  2 + 2 * (mean n Y - p) * ∑ i in range n, (Y i - mean n Y) + n * (mean n Y - p) ^ 2 := by
    rw [show n * (mean n Y - p) ^ 2 = ∑ i in range n, (mean n Y - p) ^ 2 by simp only [sum_const,
      card_range, nsmul_eq_mul], mul_sum, add_comm, ← sum_add_distrib, ← sum_add_distrib, SSE]
    congr with x
    rw [show Y x - p = (Y x - mean n Y) + (mean n Y - p) by rw [sub_add_sub_cancel]]
    ring

theorem min_sse_const_yhat_mean (hy : ∀ i, Yhat i = mean n Y) (hf : ∀ i, f i = fm)
  (hn : 0 < (n : ℚ)) (h : mean n Y ≠ fm) : SSE n Y Yhat < SSE n Y f := by
    rw [sse_rw_yhat_cons n (mean n Y) Y Yhat hy, sse_rw_yhat_cons n fm Y f hf, sub_self,
      zero_pow (by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true])]
    simp only [mul_zero, zero_mul, add_zero]
    rw [add_assoc, lt_add_iff_pos_right, sum_deviations_sub_mean_zero n Y hn, mul_zero, zero_add]
    exact Rat.instLinearOrderedCommRing.proof_3 n ((mean n Y - fm) ^ 2) hn (sq_pos_of_ne_zero
      (mean n Y - fm) (sub_ne_zero_of_ne h))

theorem min_sse_const_yhat_mean' (h : mean n Y ≠ fm) (hn : 0 < (n:ℚ)) :  SSE n Y
  (fun _ => mean n Y) < SSE n Y (fun _ => fm) := by
    simp only [sse_rw_yhat_cons', sub_self, mul_zero]
    rw [zero_pow (by positivity), zero_mul, add_zero, mul_zero, add_zero, add_assoc,
      lt_add_iff_pos_right, sum_deviations_sub_mean_zero n Y hn, mul_zero, zero_add]
    exact Rat.instLinearOrderedCommRing.proof_3 n ((mean n Y - fm) ^ 2) hn (sq_pos_of_ne_zero
      (mean n Y - fm) (sub_ne_zero_of_ne h))

theorem sse_lin_rw : SSE_lin n X Y p q = ∑ i in range n, (Y i) ^ 2 - 2 * p * ∑ i in range n,
  (Y i * X i) - 2 * q * ∑ i in range n, Y i + (p ^ 2) * ∑ i in range n, (X i) ^ 2 + 2 * p * q *
  ∑ i in range n, X i + n * q ^ 2 := by
    rw [show n * q ^ 2 = ∑ i in range n, q ^ 2 by simp only [sum_const, card_range, nsmul_eq_mul]]
    simp only [mul_sum]
    rw [show ∑ i in range n, Y i ^ 2 - ∑ i in range n, 2 * p * (Y i * X i) -
      ∑ i in range n, 2 * q * Y i = ∑ i in range n, Y i ^ 2 + -1 * ∑ i in
      range n, 2 * p * (Y i * X i) + -1 * ∑ i in range n, 2 * q * Y i by ring]
    simp only [mul_sum, ← sum_add_distrib, SSE_lin, SSE]
    congr with x
    ring_nf!

theorem func_sse_lin_rw_q : (fun q => SSE_lin n X Y p q) = fun q => ∑ i in range n, (Y i) ^ 2 - 2 *
  p * ∑ i in range n, (Y i * X i) - 2 * q * ∑ i in range n, Y i + (p ^ 2) * ∑ i in range n, (X i) ^
  2 + 2 * p * q * ∑ i in range n, X i + n * q ^ 2 := by
    congr with q
    exact sse_lin_rw n p q X Y

theorem func_sse_lin_rw_q' : ∀ q : ℚ, (fun q => SSE_lin n X Y p q) q = (fun q => ∑ i in range n,
  (Y i) ^ 2) q + (fun q => - 2 * p * ∑ i in range n, (Y i * X i)) q + (fun q => - 2 * q *
  ∑ i in range n, Y i) q + (fun q => (p ^ 2) * ∑ i in range n, (X i) ^ 2) q +
  (fun q => (2 * p * q * ∑ i in range n, X i + n * q ^ 2)) q := by
    rw [func_sse_lin_rw_q]
    intro q
    simp only [neg_mul]
    ring_nf!

theorem func_sse_lin_rw_p : (fun p => SSE_lin n X Y p q) = fun p => ∑ i in range n, (Y i) ^ 2 - 2 *
  p * ∑ i in range n, (Y i * X i) - 2 * q * ∑ i in range n, Y i + (p ^ 2) * ∑ i in range n, (X i) ^
  2 + 2 * p * q * ∑ i in range n, X i + n * q ^ 2 := by
    congr with p
    exact sse_lin_rw n p q X Y

theorem func_sse_lin_rw_p' : ∀ p : ℚ, (fun p => SSE_lin n X Y p q) p = (fun p => ∑ i in range n,
  (Y i) ^ 2) p + (fun p => - 2 * p * ∑ i in range n, (Y i * X i)) p + (fun p => - 2 * q *
  ∑ i in range n, Y i) p + (fun p => (p ^ 2) * ∑ i in range n, (X i) ^ 2) p +
  (fun p => (2 * p * q * ∑ i in range n, X i + n * q ^ 2)) p := by
    rw [func_sse_lin_rw_p]
    intro q
    simp only [neg_mul]
    ring_nf!

theorem q_deriv_sse_lin (hn : 0 < n) : deriv (fun (q : ℚ) => SSE_lin n X Y p q) q = 0 ↔
  q = mean n Y - p * mean n X := by
    simp_rw [func_sse_lin_rw_q']
    repeat (first | rw [deriv_add] | simp_all [deriv_id'', mul_one] | rw [deriv_const_mul])
    rw [show -(2 * ∑ i in range n, Y i) + (2 * p * ∑ i in range n, X i + ↑n * (2 * q))
       = 2 * (-(∑ i in range n, Y i) + (p * ∑ i in range n, X i + ↑n * (q))) by ring]
    simp only [_root_.mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    constructor <;> intro h
    · rw [mean, mean]
      rw [neg_add_eq_zero, ← sub_eq_iff_eq_add'] at h
      calc
        q = (n * q) / n := by rw [mul_comm]; field_simp
        _ = (∑ i in range n, Y i - p * ∑ i in range n, X i) / n := by rw [← h]
        _ = 1 / n * ∑ i in range n, Y i - p * (1 / n * ∑ i in range n, X i) := by ring_nf!
    · rw [h, mul_sub_left_distrib, show n * (p * mean n X) = p * (n * mean n X) by ring, mean_prod]
      rw [mean_prod]
      field_simp
      repeat exact hn
    repeat fun_prop

theorem p_deriv_sse_lin (h : deriv (fun (q : ℚ) => SSE_lin n X Y p q) q = 0) (hn : 0 < n)
  (hx : mean n (X ^ 2) ≠ (mean n X) ^ 2) :
  deriv (fun (p : ℚ) => SSE_lin n X Y p q) p = 0 ↔ p = (mean n (Y * X) - mean n Y * mean n X) /
  (mean n (X ^ 2) - (mean n X) ^ 2) := by
    have hq : q = mean n Y - p * mean n X := (q_deriv_sse_lin n p q X Y hn).mp h
    have hn' : (1 / (n : ℚ)) / (1 / n) = 1 := div_self (by
      rw [one_div, ne_eq, inv_eq_zero, cast_eq_zero, ← ne_eq]
      exact _root_.ne_of_gt hn)
    have hn'' : (n : ℚ) / n = 1 := div_self (_root_.ne_of_gt (by positivity))
    have hx' : mean n (X ^ 2) - (mean n X) ^ 2 ≠ 0 := sub_ne_zero.mpr hx
    simp_rw [func_sse_lin_rw_p']
    repeat (first | rw [deriv_add] | simp_all [deriv_id'', mul_one] | rw [deriv_const_mul])
    rw [show -(2 * ∑ i in range n, Y i * X i) + 2 * p * ∑ i in range n, X i ^ 2 +
      2 * (mean n Y - p * mean n X) * ∑ i in range n, X i = 2 * (-(∑ i in range n, Y i * X i) + p *
      ∑ i in range n, X i ^ 2 + (mean n Y - p * mean n X) * ∑ i in range n, X i) by ring]
    simp only [_root_.mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    have step1 : -∑ i in range n, Y i * X i + p * ∑ i in range n, X i ^ 2 + (mean n Y - p *
      mean n X) * ∑ i in range n, X i = 0 ↔ - mean n (Y * X) + p * mean n (X ^ 2) + (mean n Y -
      p * mean n X) * mean n X = 0 := by
        simp only [mean]
        field_simp
        ring_nf!
    have step2 : -mean n (Y * X) + p * mean n (X ^ 2) + (mean n Y - p * mean n X) * mean n X = 0 ↔
      p * (mean n (X ^ 2) - mean n X ^ 2) + (- mean n (Y * X) + mean n Y * mean n X) = 0 := by
        ring_nf!
    have step3 : - -mean n (Y * X) + -(mean n Y * mean n X) = mean n (Y * X) - (mean n Y * mean n X)
     := by ring
    rw [step1, step2, add_eq_zero_iff_eq_neg, neg_add, step3]
    constructor <;> intro h1
    · calc
        p = (p * (mean n (X ^ 2) - mean n X ^ 2)) / (mean n (X ^ 2) - mean n X ^ 2) := by field_simp
        _ = (mean n (Y * X) - mean n Y * mean n X) / (mean n (X ^ 2) - mean n X ^ 2) := by rw [h1]
    · rw [h1]
      field_simp
    repeat fun_prop

theorem lin_reg_proof
  (hp : p = (mean n (Y * X) - mean n Y * mean n X) / (mean n (X ^ 2) - (mean n X) ^ 2))
  (hq : q = mean n Y - (mean n (Y * X) - mean n Y * mean n X) / (mean n (X ^ 2) - (mean n X) ^ 2) *
    mean n X)
  (hn : 0 < n)
  (hx : mean n (X ^ 2) ≠ (mean n X) ^ 2)
  : deriv (fun (p : ℚ) => SSE_lin n X Y p q) p = 0 ∧ deriv (fun (q : ℚ) => SSE_lin n X Y p q) q = 0
  := by
    rw [← hp] at hq
    exact ⟨(p_deriv_sse_lin n p q X Y ((q_deriv_sse_lin n p q X Y hn).mpr hq) hn hx).mpr hp ,
      (q_deriv_sse_lin n p q X Y hn).mpr hq⟩

theorem lin_reg_proof'
  (h1 : deriv (fun (p : ℚ) => SSE_lin n X Y p q) p = 0)
  (h2 : deriv (fun (q : ℚ) => SSE_lin n X Y p q) q = 0)
  (hn : 0 < n)
  (hx : mean n (X ^ 2) ≠ (mean n X) ^ 2)
  : q = mean n Y - (mean n (Y * X) - mean n Y * mean n X) / (mean n (X ^ 2) - (mean n X) ^ 2) *
    mean n X := by
      have hp : p = (mean n (Y * X) - mean n Y * mean n X) / (mean n (X ^ 2) - (mean n X) ^ 2) :=
        (p_deriv_sse_lin n p q X Y h2 hn hx).mp h1
      have hq : q = mean n Y - p * mean n X := (q_deriv_sse_lin n p q X Y hn).mp h2
      rw [hq, hp]

-------------------------------------------------------------------
/- ### Testing Grounds ### -/
