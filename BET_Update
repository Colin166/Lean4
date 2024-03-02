import Mathlib

open BigOperators
open Filter
open Nat
open Set

set_option maxHeartbeats 0

/-!
# BET
This section defines the Brunauer–Emmett–Teller (BET) adsorption theory where we relax the assumption
of the [Langmuir model](./langmuir_kinetics.html) that restricts adsorption on a single site to be one molecule;
instead, molecules can stack on top of each other in layers.
-/


/-!
### Definitions
-/
--noncomputable theorem
namespace BET
structure system :=
  (C_1 C_L s₀ P₀: ℝ)
  (hCL : 0 < C_L)
  (hC1 : 0 < C_1)
  (hs₀ : 0 < s₀)
  (hP₀ : 0 < P₀)


def first_layer_adsorption_rate (S : BET.system) (P : ℝ):= (S.C_1)*P
local notation "Y" => BET.first_layer_adsorption_rate

def n_layer_adsorption_rate (S : BET.system) (P : ℝ):= (S.C_L)*P
local notation "X" => BET.n_layer_adsorption_rate

noncomputable def adsorption_constant (S: BET.system) (P : ℝ):= Y/X
local notation "C" => Y/X --BET.adsorption_constant

noncomputable def seq (S : BET.system) (P : ℝ) : ℕ → ℝ
  | 0 => S.s₀
  | (Nat.succ n) => ((X S P)^(n+1))*S.s₀*(C S P)

noncomputable def volume_adsorbed (S : BET.system) (V₀ P : ℝ) := V₀ * ∑'  (k : ℕ), ↑k * (seq S P k)
local notation "V" => BET.volume_adsorbed

noncomputable def catalyst_area (S : BET.system) (P : ℝ) := ∑' (k : ℕ), (seq S P k)
local notation "A" => BET.catalyst_area

noncomputable def brunauer_28 (S : BET.system) := λ P : ℝ => (C S P)*P/((S.P₀-P)*(1+((C S P)-1)*(P/S.P₀)))
noncomputable def brunauer_26 (S : BET.system) := λ P => (C S P)*(X S P)/((1-(X S P))*(1-(X S P)+(C S P)*(X S P)))

/-!
### Proof
-/

lemma sequence_math {S : BET.system} {P : ℝ} (hx1: (X S P) < 1) (hx2 : 0 < (X S P)) :
  (∑' k : ℕ, ((k + 1:ℕ)*(seq S P (k+1))))/(S.s₀ + ∑' k, (seq S P (k+1:ℕ))) = (C S P)*(X S P)/((1 - (X S P))*(1 - (X S P) + (X S P)*(C S P))):= by
  simp only [seq]
  have hxnorm : ‖X S P‖ < 1 := by apply abs_lt.mpr; constructor; linarith; assumption
  simp [← mul_assoc]
  rw [tsum_mul_right, tsum_mul_right, tsum_mul_right, tsum_mul_right]
  have hsig : ∑' (k : ℕ), (↑k + 1) * X S P ^ (k + 1) = X S P / (1 - X S P) ^ 2 := by
    convert tsum_coe_mul_geometric_of_norm_lt_one hxnorm using 1
    have : Function.support (fun n => n * X S P ^ (n : ℕ)) ⊆ Set.range Nat.succ := by
      rw [Function.support_subset_iff']
      simp
    rw [←tsum_subtype_eq_of_support_subset this, tsum_range (fun (n : ℕ) => n * X S P ^ n) Nat.succ_injective]; simp
  rw [hsig]; field_simp; ring_nf
  have hx2' : 0 ≤ (X S P) := by linarith
  have hsig_split : (∑' (x : ℕ), X S P ^ (x + 1)) = (∑' (x : ℕ), X S P ^ x * X S P) := by apply tsum_congr; intro x; rw [← pow_one (X S P)]; ring
  rw [hsig_split, tsum_mul_right, tsum_geometric_of_lt_one hx2' hx1, pow_two]
  have xsp_ne_zero : X S P ≠ 0 := by linarith
  have ss0_ne_zero : S.s₀ ≠ 0 := by {linarith[S.hs₀]}
  have one_sub_xsp_ne_zero : 1 - X S P ≠ 0 := by {linarith [hx1, hx2]}
  field_simp; repeat rw [← inv_mul_eq_div]
  nth_rw 2 [← mul_one (Y S P), show 1 = (1 - X S P) / (1 - X S P) by {apply Eq.symm (div_self one_sub_xsp_ne_zero)}]
  simp [*, xsp_ne_zero, one_sub_xsp_ne_zero, ss0_ne_zero]
  rw [mul_assoc (X S P) (S.s₀) (1 - X S P), mul_assoc (X S P) S.s₀ (Y S P), ← left_distrib (X S P) _ _, mul_inv, mul_comm, ← mul_assoc, ← mul_assoc]
  have step1 := by
    calc
      X S P * X S P * S.s₀ * Y S P * (1 - X S P) * (X S P)⁻¹ * (S.s₀ * (1 - X S P) + S.s₀ * Y S P)⁻¹ * (X S P - X S P * X S P * 2 + X S P ^ 3)⁻¹ = X S P * ((X S P * (X S P)⁻¹) * S.s₀) * Y S P * (1 - X S P) * (S.s₀ * (1 - X S P) + S.s₀ * Y S P)⁻¹ * (X S P - X S P * X S P * 2 + X S P ^ 3)⁻¹ := by ring
      _ = X S P * S.s₀ * Y S P * (1 - X S P) * (S.s₀ * (1 - X S P) + S.s₀ * (Y S P))⁻¹ * (X S P - X S P * X S P * 2 + X S P ^ 3)⁻¹ := by rw [show (X S P) * (X S P)⁻¹ = 1 by {apply mul_inv_cancel xsp_ne_zero}, one_mul S.s₀];
  rw [step1, ← left_distrib (S.s₀) _ _, mul_inv]
  have step2 := by
    calc
      X S P * S.s₀ * Y S P * (1 - X S P) * (S.s₀⁻¹ * (1 - X S P + Y S P)⁻¹) * (X S P - X S P * X S P * 2 + X S P ^ 3)⁻¹ = X S P * ((S.s₀) * (S.s₀)⁻¹) * Y S P * (1 - X S P) * ((1 - X S P) + Y S P)⁻¹ * (X S P - X S P * X S P * 2 + X S P ^ 3)⁻¹ := by ring
      _ = (X S P * Y S P * (1 - X S P) * ((1 - X S P) + Y S P)⁻¹ * (X S P - X S P * X S P * 2 + X S P ^ 3)⁻¹) := by rw [show ((S.s₀) * (S.s₀)⁻¹) = 1 by {apply div_self ss0_ne_zero}, mul_one]
      _ = (X S P * Y S P * (1 - X S P) * ((1 - X S P) + Y S P)⁻¹ * (X S P - X S P * X S P * 2 + X S P ^ 3)⁻¹) * (1) := by ring
  rw [step2]; apply Eq.symm; field_simp; nth_rw 1 [← mul_one (X S P * Y S P)]; nth_rw 1 [show 1 = (1 - X S P) / (1 - X S P) by apply Eq.symm (div_self one_sub_xsp_ne_zero)];
  have step3 : ((1 - X S P + Y S P) * (X S P - X S P * X S P * 2 + X S P ^ 3)) = (X S P + X S P * Y S P + (-(X S P * X S P * 2) - X S P * X S P * Y S P) + X S P ^ 3) * (1 - X S P) := by ring
  rw [step3]; field_simp; rw [mul_comm (X S P + X S P * Y S P + (-(X S P * X S P * 2) - X S P * X S P * Y S P) + X S P ^ 3) (1 - X S P), ← div_div]; field_simp


theorem regression_form
{P V₀: ℝ}
(S : BET.system)
(hx1: (X S P) < 1)
(hx2 : 0 < (X S P))
(hP : 0 < P)
:
  let a := V₀*S.C_1
  let b := S.C_L
  let c := S.C_1
  let q := (V S V₀ P)/(A S P)
  q = a*P/((1-b*P)*(1-b*P+c*P))
:= by
  intros
  have hsum2 : Summable (seq S P)
  { apply (summable_nat_add_iff 1).mp
    simp only [seq, _root_.pow_succ', mul_assoc]
    exact (summable_geometric_of_lt_one hx2.le hx1).mul_right _ }
  have hxnorm : ‖X S P‖ < 1 := by apply abs_lt.mpr; constructor; linarith; assumption
  have hsum :Summable (λ k : ℕ => ↑k * (seq S P k))
  { apply (summable_nat_add_iff 1).mp _
    simp only [seq, ← mul_assoc]
    apply Summable.mul_right _ (Summable.mul_right _ _)
    set u := λ k : ℕ => (k : ℝ) * (X S P) ^ k
    change Summable (λ (n : ℕ) => u (n+1))
    apply (summable_nat_add_iff 1).mpr _
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hxnorm }
  simp only [BET.volume_adsorbed, BET.catalyst_area]
  rw [ tsum_eq_zero_add hsum,  tsum_eq_zero_add hsum2]
  simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_one, Nat.pow_zero, one_mul, mul_assoc, Nat.cast_add, mul_div_assoc]
  have hsig : (∑' (b : ℕ), (↑b + 1) * seq S P (b + 1)) / (S.s₀ + ∑' (b : ℕ), seq S P (b + 1)) = (∑' k : ℕ, ((k + 1:ℕ)*(seq S P (k+1))))/(S.s₀ + ∑' k, (seq S P (k+1:ℕ))) := by simp [*]
  rw [show seq S P 0 = S.s₀ by {simp [seq]}, hsig, sequence_math hx1 hx2]
  simp [BET.adsorption_constant, BET.n_layer_adsorption_rate]
  have h1 : S.C_L ≠ 0 := by {linarith [S.hCL]}
  have hP : P ≠ 0 := by {linarith [hP]}
  field_simp; left; repeat rw [← inv_mul_eq_div, mul_inv]
  calc
    (1 - S.C_L * P)⁻¹ * ((1 - S.C_L * P) * (S.C_L * P) + S.C_L * P * Y S P)⁻¹ * (Y S P * (S.C_L * P)) = (1 - S.C_L * P)⁻¹ * ((1 - S.C_L * P) * (S.C_L * P) + (Y S P) * (S.C_L * P))⁻¹ * (Y S P * (S.C_L * P)) := by ring
    _ = (1 - S.C_L * P)⁻¹ * (((1 - S.C_L * P) + Y S P) * (S.C_L *P))⁻¹ * (Y S P * (S.C_L * P)) := by ring
    _ = (1 - S.C_L * P)⁻¹ * (((1 - S.C_L * P) + Y S P)⁻¹ * (S.C_L *P)⁻¹) * (Y S P * (S.C_L * P)) := by rw [mul_inv ((1 - S.C_L * P) + Y S P) (S.C_L *P)]
    _ = (1 - S.C_L * P)⁻¹ * ((1 - S.C_L * P) + Y S P)⁻¹ * (S.C_L * P) * (S.C_L *P)⁻¹ * (Y S P) := by ring
    _ = (1 - S.C_L * P)⁻¹ * ((1 - S.C_L * P) + Y S P)⁻¹ * (S.C_L * S.C_L⁻¹) * (P * P⁻¹) * (Y S P) := by ring
    _ = (1 - S.C_L * P)⁻¹ * ((1 - S.C_L * P) + Y S P)⁻¹ * (Y S P) := by rw [mul_inv_cancel h1, mul_inv_cancel hP, mul_one, mul_one]

theorem brunauer_26_from_seq
{P V₀: ℝ}
{S : BET.system}
(hx1: (X S P) < 1)
(hx2 : 0 < (X S P))
(hP : 0 < P) -- THIS IS BEING USED IN PROOF DO NOT DELETE
(hy : Y S P ≠ X S P - 1) -- THIS WAS ADDED BECAUSE THEOREM IS FALSE OTHERWISE
:  (V S V₀ P)/(A S P) = V₀*(brunauer_26 S P)
:= by
  intros
  simp [brunauer_26]
  have hsum2 : Summable (seq S P)
  { apply (summable_nat_add_iff 1).mp _
    simp only [seq, _root_.pow_succ', mul_assoc]
    exact (summable_geometric_of_lt_one hx2.le hx1).mul_right _ }
  have hxnorm : ‖X S P‖ < 1 := by apply abs_lt.mpr ; constructor <;> linarith
  have hsum : Summable (λ k : ℕ => ↑k * (seq S P k))
  { apply (summable_nat_add_iff 1).mp _
    simp only [seq, ← mul_assoc]
    apply Summable.mul_right _ (Summable.mul_right _ _)
    set u := λ k : ℕ => (k : ℝ) * (X S P) ^ k
    change Summable (λ (n : ℕ) => u (n+1))
    apply (summable_nat_add_iff 1).mpr _
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hxnorm }
  simp only [BET.volume_adsorbed, BET.catalyst_area]
  rw [tsum_eq_zero_add hsum, tsum_eq_zero_add hsum2]
  simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_one, Nat.pow_zero, one_mul, mul_assoc, Nat.cast_add, mul_div_assoc]
  rw [show seq S P 0 = S.s₀ by {simp [seq]}]
  rw [tsum_congr, sequence_math hx1 hx2]
  field_simp [mul_comm (X S P) (C S P)]
  rw [mul_comm (1 - X S P)  (X S P), ← left_distrib (X S P) (1 - X S P) (Y S P)]
  have xsp_ne_zero : X S P ≠ 0 := by apply Ne.symm (_root_.ne_of_lt hx2)
  have xsp_sub_ysp_ne_zero : (1 - X S P) + Y S P ≠ 0 := by
    intro h'
    rw [← add_right_inj (X S P - 1), add_zero] at h'
    have hc : Y S P = (X S P - 1) := by rw [← h']; ring
    contradiction
  have xsp_sub_one_ne_zero : ((1 - X S P) * (1 - X S P + Y S P)) ≠ 0 := by
    intro H
    have H' := by apply eq_zero_or_eq_zero_of_mul_eq_zero H
    rcases H' with H1 | H2
    have xsp_ne_one : X S P ≠ 1 := by apply _root_.ne_of_lt hx1
    have xsp_eq_one : X S P = 1 := by apply (add_right_inj (-X S P)).mp; ring; exact (Eq.symm H1)
    contradiction; contradiction
  repeat rw [← mul_assoc]
  rw [mul_comm (1 - X S P) (X S P),  mul_assoc (X S P)  (1 - X S P)  (1 - X S P + Y S P)];
  have hxsp' : ((1 - X S P) * (1 - X S P + Y S P))⁻¹ * (X S P)⁻¹ * X S P * ((1 - X S P) * (1 - X S P + Y S P)) = (((1 - X S P) * (1 - X S P + Y S P)) * ((1 - X S P) * (1 - X S P + Y S P))⁻¹) * ((X S P) * (X S P)⁻¹) := by ring
  have hxsp : X S P / (X S P * ((1 - X S P) * (1 - X S P + Y S P))) = 1 / ((1 - X S P) * (1 - X S P + Y S P)) := by
    apply eq_one_div_of_mul_eq_one_left;
    rw [← inv_mul_eq_div, mul_inv, mul_comm (X S P)⁻¹  ((1 - X S P) * (1 - X S P + Y S P))⁻¹, hxsp', mul_inv_cancel xsp_ne_zero, mul_one, mul_inv_cancel xsp_sub_one_ne_zero]
  have hfin : V₀ * Y S P * X S P / (X S P * ((1 - X S P) * (1 - X S P + Y S P))) = V₀ * Y S P * (X S P / (X S P * ((1 - X S P) * (1 - X S P + Y S P)))) := by ring
  rw [hfin, hxsp]; ring
  intro b
  rw [Nat.cast_add]; simp [*]

lemma tendsto_at_top_at_inv_CL (P : ℝ) (S : BET.system) (hP : 0 < P) -- hP hypothesis was added
: Filter.Tendsto (brunauer_26 S) (nhdsWithin (1/S.C_L) (Set.Ioo 0 (1/S.C_L))) Filter.atTop:= by
  have pdiv : P / P = 1 := by apply div_self (ne_of_gt hP)
  have h1 : Filter.Tendsto (λ («x» : ℝ) => 1 - S.C_L * «x») (nhds (S.C_L)⁻¹) (nhds (0)) := by
      rw [show (0 : ℝ) = 1 - 1 by norm_num]
      apply Filter.Tendsto.sub; apply tendsto_const_nhds;
      rw [show (1 : ℝ) = S.C_L*S.C_L⁻¹ by apply Eq.symm; rw [mul_inv_cancel (ne_of_gt S.hCL)]]
      apply Filter.Tendsto.const_mul
      exact fun ⦃U⦄ a => a
  have h2 : S.C_1 * P / (S.C_L * P) = S.C_1 / S.C_L := by
    rw [mul_div_mul_comm]
    simp_all only [Pi.div_apply, mul_one]
  have h : 0 < (C S P) := by
      simp [BET.adsorption_constant, BET.n_layer_adsorption_rate, BET.first_layer_adsorption_rate];
      rw [h2]
      refine div_pos S.hC1 S.hCL
  rw [show brunauer_26 S = λ P => (C S P)*(X S P)/((1-(X S P))*(1-(X S P)+(C S P)*(X S P))) by exact rfl]
  simp [BET.n_layer_adsorption_rate, BET.first_layer_adsorption_rate, *]
  apply Filter.Tendsto.mul_atTop h
  simp [BET.n_layer_adsorption_rate, BET.first_layer_adsorption_rate, h2]
  · suffices Filter.Tendsto (fun x => S.C_1 * x)
          (nhdsWithin S.C_L⁻¹ (Set.Ioo 0 S.C_L⁻¹)) (nhds (S.C_1 * S.C_L⁻¹)) by
        apply this.congr'
        rw [eventuallyEq_nhdsWithin_iff]
        filter_upwards with x hx
        have hax : S.C_L * x ≠ 0 := by aesop
        have h' : S.C_1*x / (S.C_L*x) * (S.C_L*x) = S.C_1*x * ((S.C_L*x) / (S.C_L*x)) := by
          aesop
        rw [h']
        simp_all only [Pi.div_apply, Set.mem_Ioo, ne_eq, _root_.mul_eq_zero, not_false_eq_true, div_mul_cancel, div_self,
          mul_one]
    exact tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto (Continuous.continuousAt (continuous_mul_left S.C_1)))
  · suffices Filter.Tendsto (fun x => ((1 - S.C_L * x) * (1 - S.C_L * x + S.C_1 * x))⁻¹)
        (nhdsWithin S.C_L⁻¹ (Set.Ioo 0 S.C_L⁻¹)) atTop by
      apply this.congr'
      rw [eventuallyEq_nhdsWithin_iff]
      filter_upwards with x hx
      have hax : S.C_L * x ≠ 0 := by aesop
      have h' : S.C_1*x / (S.C_L*x) * (S.C_L*x) = S.C_1*x * ((S.C_L*x) / (S.C_L*x)) := by
        aesop
      have h'' : S.C_1*x * ((S.C_L*x) / (S.C_L*x)) = S.C_1*x := by
        aesop
      rw [h',h'']
      rfl
    refine Filter.Tendsto.inv_tendsto_zero ?_
    rw [nhdsWithin]
    apply Filter.Tendsto.inf
    rw [show 0 = 0*(0 + S.C_1*S.C_L⁻¹) by simp]
    apply Filter.Tendsto.mul
    · exact h1
    · apply Filter.Tendsto.add
      · exact h1
      · apply Filter.Tendsto.const_mul
        exact fun ⦃U⦄ a => a
    refine tendsto_principal_principal.mpr ?h₂.a
    intro x hx
    rw [mem_Ioi]
    have ha : S.C_L*x < 1 := by
      rw [show 1 = S.C_L*S.C_L⁻¹ by rw [← one_div]; simp [*]; exact Eq.symm (div_self (ne_of_gt S.hCL))]
      simp_all only [mem_Ioo]
      refine (div_lt_iff' S.hCL).mp ?_
      rw [mul_comm, show x*S.C_L/S.C_L = x*(S.C_L/S.C_L) by ring]
      rw [show (S.C_L/S.C_L) = 1 by apply div_self (ne_of_gt S.hCL)]
      simp
      apply hx.2
    have hb : 0 < S.C_1*x := by
      have i1 : 0 < S.C_1 := by exact S.hC1
      aesop
    have step1 : 0 < 1 - S.C_L*x := by
      exact sub_pos.mpr ha
    have step2 : 0 < (1 - S.C_L*x + S.C_1*x) := by
      exact add_pos step1 hb
    exact Real.mul_pos step1 step2

lemma tendsto_at_bot_at_inv_CL (S : BET.system) (hCL : S.C_1 < S.C_L) {P : ℝ} (hP : 0 < P) -- hP hypothesis was added
: Filter.Tendsto (brunauer_26 S) (nhdsWithin (1/S.C_L) (Set.Ioo (1/S.C_L) (1/(S.C_L-S.C_1)))) Filter.atBot:= by
  have h1 : Filter.Tendsto (λ («x» : ℝ) => -(1 - S.C_L * «x»)) (nhds (S.C_L)⁻¹) (nhds (0)) := by
    simp [*]; rw [show (0 : ℝ) = 1 - 1 by norm_num]
    apply Filter.Tendsto.sub; rw [show (1 : ℝ) = S.C_L*S.C_L⁻¹ by {apply Eq.symm; rw [mul_inv_cancel (ne_of_gt S.hCL)]}]
    apply Filter.Tendsto.const_mul; refine Continuous.tendsto ?hf.h.hf S.C_L⁻¹; exact continuous_id'
    exact tendsto_const_nhds
  have h2 : Filter.Tendsto (λ («x» : ℝ) => 1 - S.C_L * «x») (nhds (S.C_L)⁻¹) (nhds (0)) := by
    rw [show (0 : ℝ) = 1 - 1 by norm_num]
    apply Filter.Tendsto.sub; apply tendsto_const_nhds;  rw [show (1 : ℝ) = S.C_L*S.C_L⁻¹ by apply Eq.symm; rw [mul_inv_cancel (ne_of_gt S.hCL)]]
    apply Filter.Tendsto.const_mul; refine Continuous.tendsto ?hg.h.hf S.C_L⁻¹; exact continuous_id'
  have p_div : P / P = 1 := by exact div_self (ne_of_gt hP)
  have SP_div : S.C_1 * P / (S.C_L * P) = S.C_1 / S.C_L := by
    rw [mul_div_mul_comm]
    simp_all only [neg_sub, mul_one]
  have S1_inv_gt_zero : 0 < S.C_1⁻¹ := by exact inv_pos.mpr (S.hC1)
  have SL_inv_gt_zero : 0 < S.C_L⁻¹ := by exact inv_pos.mpr (S.hCL)
  have h : 0 < (C S P) := by simp [BET.adsorption_constant, BET.first_layer_adsorption_rate, BET.n_layer_adsorption_rate, mul_div_mul_right S.C_1 S.C_L (ne_of_gt hP), div_pos S.hC1 S.hCL];
  simp only [brunauer_26, BET.n_layer_adsorption_rate, div_eq_inv_mul]
  rw [show brunauer_26 S = λ P => (C S P)*(X S P)/((1-(X S P))*(1-(X S P)+(C S P)*(X S P))) by exact rfl]
  simp [BET.n_layer_adsorption_rate, BET.first_layer_adsorption_rate, *]
  apply Filter.Tendsto.mul_atBot h
  simp [BET.n_layer_adsorption_rate, BET.first_layer_adsorption_rate, SP_div]
  · suffices Tendsto (fun x => S.C_1 * x) (nhdsWithin S.C_L⁻¹ (Ioo S.C_L⁻¹ (S.C_L - S.C_1)⁻¹)) (nhds (S.C_1 / S.C_L)) by
      apply this.congr'
      rw [eventuallyEq_nhdsWithin_iff]
      filter_upwards with x hx
      apply Eq.symm
      rw [mem_Ioo] at hx
      have x_gt_zero : 0 < x := by linarith
      have SLx_div_self : ((S.C_L * x) / (S.C_L * x)) = 1 := by
        refine div_self ?_
        aesop
      calc
        S.C_1 * x / (S.C_L * x) * (S.C_L * x) = S.C_1 * x * ((S.C_L * x) / (S.C_L * x)) := by ring
        _ = S.C_1 * x := by simp [*]
    rw [show S.C_1 / S.C_L = S.C_1*S.C_L⁻¹ by ring]
    apply Filter.Tendsto.const_mul
    exact tendsto_nhdsWithin_of_tendsto_nhds fun ⦃U⦄ a => a
  · suffices Filter.Tendsto (fun x => ((1 - S.C_L * x) * (1 - S.C_L * x + S.C_1 * x))⁻¹)
        (nhdsWithin (S.C_L⁻¹) (Set.Ioo (S.C_L⁻¹) ((S.C_L-S.C_1)⁻¹))) atBot by
      apply this.congr'
      rw [eventuallyEq_nhdsWithin_iff]
      filter_upwards with x hx
      rw [mem_Ioo] at hx
      have x_gt_zero : 0 < x := by linarith
      have Sx_ne_zero : S.C_L*x ≠ 0 := by aesop
      have h' : S.C_1*x / (S.C_L*x) * (S.C_L*x) = S.C_1*x * ((S.C_L*x) / (S.C_L*x)) := by
        aesop
      have h'' : S.C_1*x * ((S.C_L*x) / (S.C_L*x)) = S.C_1*x := by
        aesop
      rw [h',h'']
      rfl
    rw [← tendsto_neg_atTop_iff]
    suffices Tendsto (fun x => (-(1 - S.C_L * x) * (1 - S.C_L * x + S.C_1 * x))⁻¹)
      (nhdsWithin S.C_L⁻¹ (Ioo S.C_L⁻¹ (S.C_L - S.C_1)⁻¹)) atTop by
      apply this.congr'
      rw [eventuallyEq_nhdsWithin_iff]
      filter_upwards with x hx
      rw [neg_inv, neg_mul]
    refine Filter.Tendsto.inv_tendsto_zero ?_
    rw [nhdsWithin]
    apply Filter.Tendsto.inf
    rw [show 0 = 0*(0 + S.C_1*S.C_L⁻¹) by rw [zero_mul]]
    apply Filter.Tendsto.mul
    · exact h1
    · apply Filter.Tendsto.add
      · exact h2
      · apply Filter.Tendsto.const_mul
        exact fun ⦃U⦄ a => a
    refine tendsto_principal_principal.mpr ?_
    intro x hx
    rw [mem_Ioi, neg_sub]
    rw [mem_Ioo] at hx
    rcases hx with ⟨l1, l2⟩
    have x_gt_zero : 0 < x := by linarith
    have hl1 : S.C_L*S.C_L⁻¹ < S.C_L*x := by aesop
    rw [show S.C_L*S.C_L⁻¹ = 1 by rw [mul_comm]; apply (inv_mul_cancel (ne_of_gt S.hCL))] at hl1
    have hl2 : 0 < S.C_L*x - 1 := by linarith
    have hr1 : (S.C_L - S.C_1) * x < (S.C_L - S.C_1)*(S.C_L - S.C_1)⁻¹ := by aesop
    rw [show (S.C_L - S.C_1)*(S.C_L - S.C_1)⁻¹ = 1 by rw [mul_comm]; refine inv_mul_cancel (by linarith)] at hr1
    have hr2 : 0 < (1 - S.C_L * x + S.C_1 * x) := by linarith
    exact Real.mul_pos hl2 hr2

lemma tendsto_at_bot_at_inv_CL' (S : BET.system) (hCL : S.C_L ≤ S.C_1) {P : ℝ} (hP : 0 < P)
: Filter.Tendsto (brunauer_26 S) (nhdsWithin (1/S.C_L) (Set.Ioi (1/S.C_L))) Filter.atBot:= by
  have p_div : P / P = 1 := by exact div_self (ne_of_gt hP)
  have SP_div : S.C_1 * P / (S.C_L * P) = S.C_1 / S.C_L := by
    rw [mul_div_mul_comm]
    simp_all only [neg_sub, mul_one]
  have CL_gt_zero : 0 < S.C_L := by
    apply S.hCL
  have inv_CL_gt_zero : 0 < S.C_L⁻¹ := by
    exact inv_pos.mpr CL_gt_zero
  have h1 : Filter.Tendsto (λ («x» : ℝ) => -(1 - S.C_L * «x»)) (nhds (S.C_L)⁻¹) (nhds (0)) := by
      simp [*]; rw [show (0 : ℝ) = 1 - 1 by norm_num]
      apply Filter.Tendsto.sub; rw [show (1 : ℝ) = S.C_L*S.C_L⁻¹ by apply Eq.symm; rw [mul_inv_cancel (ne_of_gt S.hCL)]]
      apply Filter.Tendsto.const_mul; refine Continuous.tendsto ?hf.h.hf S.C_L⁻¹; exact continuous_id'
      apply tendsto_const_nhds
  have h2 : Filter.Tendsto (λ («x» : ℝ) => 1 - S.C_L * «x») (nhds (S.C_L)⁻¹) (nhds (0)) := by
      rw [show (0 : ℝ) = 1 - 1 by norm_num]
      apply Filter.Tendsto.sub; apply tendsto_const_nhds;  rw [show (1 : ℝ) = S.C_L*S.C_L⁻¹ by {apply Eq.symm; rw [mul_inv_cancel (ne_of_gt S.hCL)]}]
      apply Filter.Tendsto.const_mul; refine Continuous.tendsto ?hf.h.hf S.C_L⁻¹;
  have h : 0 < (C S P) := by simp [BET.adsorption_constant, BET.first_layer_adsorption_rate, BET.n_layer_adsorption_rate, mul_div_mul_right S.C_1 S.C_L (ne_of_gt hP), div_pos S.hC1 S.hCL];
  simp only [brunauer_26, BET.n_layer_adsorption_rate, div_eq_inv_mul]
  rw [show brunauer_26 S = λ P => (C S P)*(X S P)/((1-(X S P))*(1-(X S P)+(C S P)*(X S P))) by exact rfl]
  simp [*, BET.n_layer_adsorption_rate, BET.first_layer_adsorption_rate]
  suffices Tendsto (fun P => S.C_1 * P / ((1 - S.C_L * P) * (1 - S.C_L * P + S.C_1 * P)))
    (nhdsWithin S.C_L⁻¹ (Set.Ioi S.C_L⁻¹)) atBot by
      apply this.congr'
      rw [eventuallyEq_nhdsWithin_iff]
      filter_upwards with x hx
      have x_gt_zero : 0 < x := by
        rw [show x ∈ Set.Ioi S.C_L⁻¹ ↔ S.C_L⁻¹ < x by exact
          { mp := fun a => hx, mpr := fun a => hx }] at hx
        linarith
      have SCL_x_div : (S.C_L * x) / (S.C_L * x) = 1 := by
        refine div_self ?_
        aesop
      have h' : S.C_1*x / (S.C_L*x) * (S.C_L*x) = S.C_1*x * ((S.C_L*x) / (S.C_L*x)) := by
        aesop
        calc
          S.C_1 * x / (S.C_L * x) * (S.C_L * x) = S.C_1 * x * ((S.C_L * x) / (S.C_L * x)) := by ring
          _ = S.C_1*x := by aesop
      rw [h']
      simp_all only [Pi.div_apply, Set.mem_Ioo, ne_eq, _root_.mul_eq_zero, not_false_eq_true, div_mul_cancel, div_self,
        mul_one]
  apply Filter.Tendsto.mul_atBot h
  · simp [*, BET.n_layer_adsorption_rate, BET.first_layer_adsorption_rate]
    rw [← inv_mul_eq_div, mul_comm]
    apply Filter.Tendsto.const_mul
    exact tendsto_nhdsWithin_of_tendsto_nhds fun ⦃U⦄ a => a
  · rw [← tendsto_neg_atTop_iff]
    suffices Tendsto (fun x => (-(1 - S.C_L * x) * (1 - S.C_L * x + S.C_1 * x))⁻¹)
      (nhdsWithin S.C_L⁻¹ (Ioi S.C_L⁻¹)) atTop by
      apply this.congr'
      rw [eventuallyEq_nhdsWithin_iff]
      filter_upwards with x hx
      rw [show (-(1 - S.C_L * x) * (1 - S.C_L * x + S.C_1 * x))⁻¹ = ((-1)*(1 - S.C_L * x) * (1 - S.C_L * x + S.C_1 * x))⁻¹ by ring]
      rw [mul_inv, mul_inv]
      rw [show (-1)⁻¹ * (1 - S.C_L * x)⁻¹ * (1 - S.C_L * x + S.C_1 * x)⁻¹ = -((1 - S.C_L * x)⁻¹ * (1 - S.C_L * x + S.C_1 * x)⁻¹) by ring]
      rw [← mul_inv]
      exact rfl
    refine Filter.Tendsto.inv_tendsto_zero ?_
    rw [nhdsWithin]
    apply Filter.Tendsto.inf
    rw [show 0 = 0*(0 + S.C_1*S.C_L⁻¹) by rw [zero_mul]]
    apply Filter.Tendsto.mul
    · exact h1
    · apply Filter.Tendsto.add
      · exact h2
      · apply Filter.Tendsto.const_mul
        exact fun ⦃U⦄ a => a
    refine tendsto_principal_principal.mpr ?_
    intro x hx
    rw [mem_Ioi] at *
    rw [neg_sub]
    have x_gt_zero : 0 < x := by linarith
    have hl1 : S.C_L*S.C_L⁻¹ < S.C_L*x := by aesop
    rw [show S.C_L*S.C_L⁻¹ = 1 by rw [mul_comm]; apply (inv_mul_cancel (ne_of_gt S.hCL))] at hl1
    have hl2 : 0 < S.C_L*x - 1 := by linarith
    have hr1 : S.C_L*x ≤ S.C_1*x := by aesop
    have hr2 : 0 < (1 - S.C_L * x + S.C_1 * x) := by linarith
    exact Real.mul_pos hl2 hr2

theorem brunauer_28_from_seq
{P V₀: ℝ}
(S : BET.system)
(h27 : S.P₀ = 1/S.C_L)
(hx1: (X S P) < 1)
(hx2 : 0 < (X S P))
(hP : 0 < P)
(hy : Y S P ≠ X S P - 1)
: (V S V₀ P)/(A S P) = V₀*(brunauer_28 S P) := by

  have  h1 : (V S V₀ P)/(A S P) = V₀*(brunauer_26 S P) := by apply brunauer_26_from_seq hx1 hx2 hP hy
  simp [*]; left
  dsimp [brunauer_26, brunauer_28, first_layer_adsorption_rate, n_layer_adsorption_rate];
  apply Eq.symm; rw [h27, ← mul_one (S.C_1 * P)]
  nth_rw 1 [show 1 = S.C_L / S.C_L by apply Eq.symm (div_self (ne_of_gt S.hCL))]; rw [mul_one]
  have step1 : S.C_1 * P / (S.C_L * P) = S.C_1 * (P / (S.C_L * P)) := by ring
  have step2 : P / (S.C_L * P) = 1 / S.C_L := by rw [← inv_mul_eq_div, mul_inv, mul_assoc, show P⁻¹ * P = 1 by rw [mul_comm, mul_inv_cancel (ne_of_gt hP)]]; simp [*]
  have step3 : S.C_1 * (1 / S.C_L) * (S.C_L * P) / ((1 - S.C_L * P) * (1 - S.C_L * P + S.C_1 * (1 / S.C_L) * (S.C_L * P))) = S.C_1 * ((1 / S.C_L) * (S.C_L * P)) / ((1 - S.C_L * P) * (1 - S.C_L * P + S.C_1 * ((1 / S.C_L) * (S.C_L * P)))) := by ring
  have step4 : (1 / S.C_L) * (S.C_L * P) = P := by rw [mul_comm S.C_L P, mul_comm, ← inv_mul_eq_div, mul_one, mul_assoc, show S.C_L * S.C_L⁻¹ = 1 by apply mul_inv_cancel (ne_of_gt S.hCL), mul_one]
  --simp [*, show P/P = 1 by apply div_self (ne_of_gt hP), show S.C_L / S.C_L = 1 by apply div_self (ne_of_gt S.hCL), show S.C_1 / S.C_1 = 1 by apply div_self (ne_of_gt S.hC1)]
  rw [show S.C_L / S.C_L = 1 by apply div_self (ne_of_gt S.hCL), mul_one, step1, step2, step3, step4]; field_simp
  have step5 : (S.C_L * ((1 / S.C_L - P) * (1 + (S.C_1 / S.C_L - 1) * (P * S.C_L)))) =  ((1 - S.C_L * P) * (1 - S.C_L * P + S.C_1 * P)) := by
    ring
    have step5_1 : S.C_L * S.C_L⁻¹ - S.C_L * P + (-(S.C_L ^ 2 * S.C_L⁻¹ * P) - S.C_L ^ 2 * S.C_L⁻¹ * P ^ 2 * S.C_1) +S.C_L ^ 2 * S.C_L⁻¹ ^ 2 * P * S.C_1 + S.C_L ^ 2 * P ^ 2 = (S.C_L * S.C_L⁻¹) - S.C_L * P + (-((S.C_L ^ 2 * S.C_L⁻¹) * P) - (S.C_L ^ 2 * S.C_L⁻¹) * P ^ 2 * S.C_1) + (S.C_L ^ 2 * S.C_L⁻¹ ^ 2) * P * S.C_1 + S.C_L ^ 2 * P ^ 2 := by ring
    have step5_2 : S.C_L * S.C_L⁻¹ = 1 := by apply mul_inv_cancel (ne_of_gt S.hCL)
    have step5_3 : S.C_L^2 * S.C_L⁻¹ = S.C_L := by rw [show S.C_L^2 = S.C_L * S.C_L by ring, mul_assoc, mul_inv_cancel (ne_of_gt S.hCL), mul_one]
    have step5_4 : S.C_L^2 * S.C_L⁻¹ ^ 2 = 1 := by rw [sq, sq, show S.C_L * S.C_L * (S.C_L⁻¹ * S.C_L⁻¹) = (S.C_L * S.C_L⁻¹) * (S.C_L * S.C_L⁻¹) by ring, step5_2, one_mul]
    rw [step5_1, step5_2, step5_3, step5_4]; ring
  rw [step5]

end BET
