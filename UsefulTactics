import Mathlib

/-!
# UsefulTactics.lean

This file lists useful tactics for the beginning Lean 4 theorem prover and is formatted to be
  helpful to both mathematicians and non-mathematicians (engineers and scientists). The tactics are
  split into major categories each showcasing a variety of tactics with their variations and
  accompanying examples, practice problems, and solutions for learning. Please note that this file
  vastly oversimplifies the actual programming going on here and the categories themselves can be
  debated as some tactics can overlap in two or more categories. However, this file is intended
  only as a beginner resource and a light appendix, nothing more.
-/

open Real Nat BigOperators Finset Set Filter
variable (x y ε δ : ℝ) (p q : ℚ) (n m k : ℕ) (P Q R : Prop) (f g : ℕ → ℝ) (A B : Set α)


/- # Bookkeeping #
These tactics are useful for organizing Lean infoview and they do not necessarily impact the proof
  in any way. A list of tactics showcased are below:
  ⬝ clear : Deletes a hypothesis from the infoview, useful for organizing the infoview
  ⬝ clear! : Deletes the hypothesis and all corresponding hypotheses
  ⬝ show_term : Shows the user what steps the tactic is doing in the infoview
  ⬝ rename_i : Renames a unnamed variable / hypothesis that appear as an italicized word with a
    cross
-/

example (hx : 0 < x) (hy : 0 < y) : 0 < x * y + 1 := by
  have hxy : 0 < x * y := Real.mul_pos hx hy
  clear hx -- deletes hx
  clear hy -- deletes hy
  exact add_pos hxy (by positivity)

example (hm : 0 < m) : n ∣ m → n < m ∨ n = m := by
  show_term aesop -- shows the user what aesop is doing in the infoview
  -- TIP : You should never do what I did. One should never use aesop in a non-terminal manner; if it didn't
  -- solve the goal don't use it.
  rw [← le_iff_lt_or_eq]
  refine le_of_dvd hm a

example (hx : 0 < x) (hy : 0 ≠ y) : x + y - x * y / (x * y) = x + y - x ^ 0 := by
  rw [pow_zero]
  show_term field_simp -- shows what field_simp did to complete the goal

example : ∀ n : ℕ, ∃ m : ℕ, n + m = n := by
  intros
  rename_i n -- renames n✝ to n
  use 0
  rw [add_zero]

/- # Rewriting #
These tactics are useful for replacing / rewriting terms in a hypothesis or goal as a different
  term or as a different form of itself. When an `at` is added to the end of the tactic, it is used
  to specify where the rewriting should occur e.g. `nth_rw 2 [hy] at hx` tells Lean to rewrite the
  second pattern of hy in the hypothesis hx. The tactics shown in this section are shown below:
  · nth_rw : Rewrites the n-th term of the pattern
  · dsimp : Replaces a term with its definition
  · rel : Does a similar thing to `rw` where it rewrites a term, but used for inequalities
  ⬝ rw : Rewrites a term by replacing it will an equivalent value
  · rw [show _ by _] : Does rewrite on an ad hoc hypothesis that the user proves in the show
      statement
  · simp : Simplifies a term using inputted lemma(s)
    · simp [*] : Uses all the lemmas in Mathlib that are marked `@simp`
    · simp_all : Is a stronger version of `simp [*]`
  · simp_rw : Simp and rw; allows the user to manipulate the interior of function definitions, sums,
      etc.

Styling Notes : You should only ever use the `only` version of a `simp` or `dsimp` call to reduce
  runtime. That means `simp_all` and `simp [*]` should be avoided entirely in professional work.
-/

example (hy : y = 2) : y * x ^ y / y = x ^ 2 := by
  nth_rw 2 [hy] -- replaces the second instance of y (x^y) with 2 (x^2)
  rw [mul_comm] -- rewrites the order of the multiplication using the commutation lemma `mul_comm`
  simp only [mul_div_assoc] -- rewrites x^2 * y/y to x^2*(y/y) using the lemma `mul_div_assoc`
  rw [show y / y = 1 by apply div_self (by linarith)] -- the `show` tactic is useful for proving
    -- the goal directly in the `rw []` statement
  simp only [rpow_two, mul_one]

def OneSet (S : Set ℕ) : Prop := ∀ s ∈ S, s = 1

example : S = {1} → OneSet S := by
  dsimp only [OneSet] -- replaces the OneSet term with its definition
  rintro h s hs
  rw [h] at hs -- rewrites h at hs; notice how the Set S becomes {1}
  exact hs

example (hx : 0 < x) (hx1 : y * x / x < 3) : -6 < -2*y := by
  rw [mul_div_assoc] at hx1 -- rewrites the hx1 hypothesis with the lemma `mul_div_assoc`
  rw [show x / x = 1 by exact div_self (ne_of_gt hx), mul_one] at hx1
  clear hx
  rw [neg_mul, neg_lt_neg_iff]
  calc
    2 * y = y + y := by ring
    _   < 3 + 3 := by rel [hx1] -- replaces the y with its inequality in hx1
    _   = 6 := by norm_num

/- # Manipulation #
These tactics change the hypothesis or goal completely by transforming it into a different theorem
  and may sometimes solve the goal directly. Some tactics separate hypotheses into smaller, easier
  to use hypotheses or generate new hypotheses. The tactics shown in this section are shown below:
  · apply : attempts to solve the goal with the given theorem
  · assumption : attempts to solve the goal using an already proved hypothesis
  · exact : attempts to solve the goal with the given theorem but gives an error if it can't
      complete the goal
  · filter_upwards with : specifically useful for Filter / limit proofs
  · have : sets up an intermediate proof to show a fact that can be used later in the proof and is
      helpful in organizing proofs
  · obtain : separates hypotheses into individual hypotheses or produce a witness for a "forall" ∀
      in a hypothesis
  · rcases : does the same as obtain
  · refine : same as apply but gives the option to set a hypothesis of a lemma as a goal
  · rfl : tells Lean that two objects are equivalent
  · suffices : sets up a separate tactic space to prove a separate future goal

Styling Notes : `exact` should be used if the goal is cleared by the lemma. `apply` should be used
  if it changes the goal, but does not clear it. `refine` should not be used in professional work.
-/

example [TopologicalSpace α] (h : IsOpen A) : IsClosed Aᶜ := by
  exact isClosed_compl_iff.mpr h -- "exact" applies the exact lemma needed to close the goal but
    -- gives an error if it can't fully close it

-- TIP : The above goal can be written as such instead removing the need for a tactic block.
example [TopologicalSpace α] (h : IsOpen A) : IsClosed Aᶜ := isClosed_compl_iff.mpr h

example : Tendsto (fun x:ℝ => (x^(2:ℝ) - 1)⁻¹) (nhdsWithin 1 (Set.Ioo 1 2)) atTop
  := by
    suffices Tendsto (fun x:ℝ => ((x + 1)*(x - 1))⁻¹) (nhdsWithin 1 (Set.Ioo 1 2)) atTop by
      -- allows us to show that the above is equivalent to the original goal
      apply this.congr'
      rw [eventuallyEq_nhdsWithin_iff]
      filter_upwards with x _
      -- Useful for filter proofs but I'm not sure what it exactly does
      field_simp
      ring
    refine Filter.Tendsto.inv_tendsto_zero ?_
    -- applies the lemma above and changes the goal to the hypothesis of that lemma
    rw [nhdsWithin]
    apply Filter.Tendsto.inf
    -- changes the goal directly by using a lemma from Mathlib
    · rw [show (0:ℝ) = (1+1)*(1 - 1) by ring]
      apply Filter.Tendsto.mul
      · apply Filter.Tendsto.add
        · exact fun ⦃U⦄ a => a
        · exact tendsto_const_nhds
      · apply Filter.Tendsto.sub
        · exact fun ⦃U⦄ a => a
        · exact tendsto_const_nhds
    · refine tendsto_principal_principal.mpr ?h₂.a
      intro x hx
      rw [Set.mem_Ioi]
      rcases hx with ⟨hx1, hx2⟩
      -- separates hx into two independent useful hypotheses
      have h1 : 0 < x + 1 := by linarith
      -- sets up an intermediate step for the proof that can be useful later
      aesop

/- # Logic #
These tactics focus on manipulating the logic in goals such as 'for all' (∀), 'exists' (∃), 'exists
  an unique' (∃!) as well as implications such as 'implies' (→) and 'if and only if' (↔). They also
  handle Boolean logic such as 'and' (∧) and 'or' (∨). They are helpful for simplifying or
  rewriting the logical statements in a goal or hypothesis into a more pilable form. The tactics
  shown in this section include:
  · by_contra : Transforms the goal into an opposite logical hypothesis and makes a new goal of
      `False` so a contradiction proof can begin
  · contradiction : Solves a `False` goal by showing a contradiction in the hypotheses
  · contrapose : Allows the user to prove the contrapositive of the statement i.e. transforms
      P → Q into ¬ Q → ¬ P
  · constructor : Separates `and` / ∧ goals into two separate goals. Also useful in separating iff
      statements into two separate implications
  · exfalso : Transforms the goal into False
  · existsi : Does a similar thing as `use` does. As far as I know, `use` is better
  · intro : Introduces a variable / hypothesis from a for all statement in a goal
  · intros : Repeatedly does the intro tactic, but will not name them, so rename_i is suggested to
      be used in conjunction
  · left : For an or `∨` goal, tells Lean that user wishes to prove the left side of the statement
  · qify : Transforms propositions from a lower number type to the Rationals
  · right : For an or `∨` goal, tells Lean that user wishes to prove the right side of the statement
  · rify : Transforms propositions from number type Nat, Int, or Rat to Real. Useful for dealing
      with divisions
  · use : Provides a witness to use in existential goals `∃`
  · zify : Transforms propositions from Number Type to Int, especially useful for subtraction,
      since Nat doesn't work with subtraction very well
-/

example (h : 1 = 0) : ((x < y → -2 * x > -2 * y) ∨ 0 = 1) ∧ 1 = 0 := by
  constructor -- dismantles the add statement into two hypotheses
  · left -- sets the left side of the or statement as the goal
    contrapose -- reverses the implication using contrapositive
    rw [not_lt, not_lt, neg_mul, neg_mul]
    intro h -- takes out the implication as a hypothesis and names it h
    linarith
  · exfalso -- transforms the goal into false
    contradiction -- proves the goal is false because 1 ≠ 0

-- TIP : Anything can be proven to be true when our hypotheses are false. This is known as a vacuous
-- truth. The above can be simplified to.
example (h : 1 = 0) : ((x < y → -2 * x > -2 * y) ∨ 0 = 1) ∧ 1 = 0 := by contradiction

example : ∃! (n : ℂ), n + 1 = 2 := by
  use 1 -- provides 1 as the witness to the existance statement
  constructor
  · zify -- turns the fun into a numerical statement
    norm_num
  · intro y
    zify
    intro hy
    calc
      y = (y + 1) - 1 := by ring
      _ = 2 - 1 := by rw [hy]
      _ = 1 := by norm_num

example : ∀ ε > 0, ∃ δ > 0, ‖x - y‖ < δ → ‖x + 1 - (y + 1)‖ < ε := by
  norm_num
  intro ε hε -- Takes out the forall statement as a number and a hypothesis
  use ε -- proves a witness for the existential quantifier
  constructor
  · assumption
  · intro h
    assumption


/- # Combination #
These tactics perform a combination of tactics to best simplify and solve the goal. Reminder: use
  the tactic `show_term` to see exactly what the combination tactic did. The tactics shown in this
  section are shown below:
  · abel : Used for Abelian groups
  · aesop : Useful for solving seemingly simple goals that one does not know the lemmas for
  · calc : Sets up a `calc` block in which the user can write a line-by-line proof
  · field_simp : Used for fields and thus is useful for statements including a division
  · fun_prop : Used for basic differential statements
  · gcongr : Useful for linear inequalities
  · linarith : Useful for linear equations and especially linear inequalities
    · nlinarith [hx, hy] : Stronger version of `linarith` that can deal with nonlinear inequalities;
      that can be supplemented with hypotheses.
  · omega : Useful for proving properties about natural numbers
  · polyrith : Useful for polynomial expressions
  · positivity : Proves goals such as `0 ≤ x`, `0 ≠ x`, `0 < x` using preexisting lemmas /
      hypotheses
  · ring : Used for rings and is especially useful for dealing with arithmetic goals
    · ring! : Stronger version of `ring`
    · ring_nf : Can be used when goal is not completed by `ring` alone
    · ring_nf! : Stronger version of `ring_nf`
  · tauto : Used for logical goals and executes several lemmas and tactics to prove logical
      equivalence

Styling Notes : One should use `nlinarith` in the place of `linarith`. `field_simp` should only be
  used when writing proofs about rational, real, and complex numbers as those are proper fields.
  Natural and integer numbers are not fields, and are instead rings. If you can, try to avoid using
  these tactics as they increase runtime by a lot; one should instead opt for more specific tactics
  that tell Lean exactly what to do to prove the goal. For example, `rw` and `exact` are much
  preferred over `ring_nf!` and `field_simp`.
-/

example (hw : w ∈ Ioo (0:ℝ) z) (hz : 0 < z) (hx : x ∈ Ioo (0 : ℝ) (z/2)) (hy : y ∈ Ioo w (z - 1)) :
  (1 + w*x/x) * y < z^2 - 1 := by
    aesop -- Again one should not do this; it's ugly and bad for runtime. I include here just for
    -- demonstration
    ring_nf
    field_simp
    nlinarith

example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by tauto

example (hx : x < y - 3) : 2 + x < y - 1 := by linarith

example (h : n < m) : n + 2 < 3 * m := by omega


/- # Cases #
These tactics separate the goal into steps (i.e. cases) that can be solved individually. If the
  goal is true for each one of those steps then if must be true for the summa of those steps. Some
  of these tactics can also be used elsewhere such as in the functional programming side of Lean
  (e.g. `match _ with`) as a method of pattern matching. Some examples of cases tactics are listed
  below:
  · cases : Splits the goal into cases
  · by_cases : Allows one to generate two hypotheses with a given name with two corresponding goals
      one goal when the hypothesis is true and another when the hypothesis is false
  · fin_cases
  · induction : Splits the goal into cases (as far as I know it does the same thing as cases)
-/
example : ∀ n : ℕ, 0 ≤ n ∧ ∃ m, n = m := by
  intro n
  cases n -- splits the natural number n into n = 0 and 0 < n
  · norm_num
  · norm_num

example (n : ℕ) : ∑ i in Finset.range (n + 1), i = n * (n + 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    symm
    apply Nat.div_eq_of_eq_mul_right two_pos
    rw [Finset.sum_range_succ, ih, mul_add 2]
    rw [show n + 1 + 1 = n + 2 by rw [Nat.add_right_cancel_iff]]
    have hle : 2 * (n + 1) ≤ (n + 1) * (n + 2) := by
      have : 0 < n + 1 := by
        rw [← Nat.succ_eq_add_one]
        exact Nat.zero_lt_succ n
      rw [mul_comm, mul_le_mul_left this]
      exact Nat.le_add_left 2 n
    have heven : 2 ∣ n * (n + 1) := by
      cases Nat.even_or_odd n with
      | inl h => exact h.two_dvd.mul_right _
      | inr h => exact (h.add_odd odd_one).two_dvd.mul_left _
    rw [← Nat.sub_eq_iff_eq_add hle, ← Nat.mul_div_assoc _ heven, eq_comm]
    apply Nat.div_eq_of_eq_mul_right two_pos
    rw [eq_comm, mul_tsub, Nat.sub_eq_iff_eq_add (Nat.mul_le_mul_left _ hle)]
    ring


/- # Questions #
These tactics do not directly change anything in the goal or in the hypotheses and are instead
  intended to offer guidance to the user on what theorems to use to prove the goal. They always
  have a question mark at the end of their respective tactic and will load options into the Lean
  infoview. Questions tactics are listed here:
  · apply?
  · aesop?
  · exact?
  · rw?
  · simp?
  No examples will be given, but to use these tactics simply insert the respective questions tactic
  with the original tactic.
-/

/- # Practice Problems #
Use as many tactics as you can to solve these problems. Try to challenge yourself by doing the
  proof in the shortest amount of lines, in the most creative way, et cetera. My solutions are in
  the section below, but the great thing about Lean 4 is that it will check any solution for
  accuracy.
-/

example (hx : 0 < x) (hy : 0 < y) : sqrt (x*y) ≤ (x + y)/2 := by
  sorry

example : ¬ (P ∧ Q ∧ R) ↔ (P → (¬ Q ∨ ¬ R)) := by
  sorry

example : ∀ ε > 0, ∃ δ < 0, ∃ n : ℕ, ε + δ = 0 → δ < ε*n := by
  sorry

example : ∃! x : ℝ, 2*x + 1 = 4*x - 3 := by
  sorry

example : 0 ≤ ∑ i in range n, f i^2 := by
  sorry

example (h : ∀ i, f i = g i) : ∑ i in range (n + 1), f i = ∑ i in range (n + 1), g i := by
  sorry

example (S : Set ℕ) : 0 ≤ ∑ᶠ i ∈ S, i := by
  sorry

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  sorry

example : ∀ S : Set α, ∅ ⊆ S := by
  sorry

example : (A ∩ Aᶜ) = ∅ := by
  sorry

example : (A ∪ B)ᶜ = (Aᶜ ∩ Bᶜ) := by
  sorry

example (hy : 0 < y) :
  Tendsto (fun x => (y*x - 1)⁻¹)
  (nhdsWithin (y⁻¹) (Set.Ioo 0 (y⁻¹))) atBot := by
    sorry

/- # Solutions #
Here are my solutions to the above practice problems. Have in mind that there are many, many ways
  to prove the practice problems above and your solution will most likely not look like mine.
  -/

example (hx : 0 < x) (hy : 0 < y) : sqrt (x*y) ≤ (x + y)/2 := by
  have h : 0 ≤ (x - y)^2 := by exact sq_nonneg (x - y)
  refine sqrt_le_iff.mpr ?_
  constructor
  · linarith
  · rw [div_pow]
    norm_num
    rw [show (x * y ≤ (x + y) ^ 2 / 4) ↔ (4 * (x * y) ≤ 4 * ((x + y) ^ 2 / 4)) by
      simp only [gt_iff_lt, zero_lt_four, _root_.mul_le_mul_left]]
    linarith

example : ¬ (P ∧ Q ∧ R) ↔ (P → (¬ Q ∨ ¬ R)) := by
  rw [← not_and_or, ← not_and]
  -- can also be solved with `tauto`

example : ∀ (ε : ℝ), ∃ (δ : ℝ), ∃ (n : ℕ), 0 < ε ∧ δ < 0 ∧ ε + δ = 0 → δ < ε*n := by
  intro ε
  use -ε
  existsi 1
  intro h
  aesop

example : ∃! x : ℝ, 2*x + 1 = 4*x - 3 := by
  existsi 2
  constructor
  · norm_num
  · intro y hy
    rw [← eq_sub_iff_add_eq'] at hy
    linarith

example : 0 ≤ ∑ i in range n, f i^2 := by
  rw [show (0:ℝ) = ∑ i in range n, 0 by aesop]
  refine sum_le_sum ?h
  intro i _
  apply sq_nonneg

example (h : ∀ i, f i = g i) :
  ∑ i in range (n + 1), f i = ∑ i in range (n + 1), g i
    := by exact sum_congr rfl fun x _ => h x

example (S : Set ℕ) : 0 ≤ ∑ᶠ i ∈ S, i := by
  simp only [_root_.zero_le]

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  apply subset_antisymm
  · intro a ha
    rcases ha with ha1 | ha2
    · constructor
      <;> {left; assumption}
    · constructor
      <;> {right; obtain ⟨h1, h2⟩ := ha2; assumption}
  · intro a ha
    rcases ha with ⟨ (ha1 | ha2), (ha3 | ha4) ⟩
    repeat (first | left; assumption)
    right
    tauto

example : ∀ S : Set α, ∅ ⊆ S := by
  intro S a
  contrapose
  intros
  exact fun a => a -- obtained from apply? tactic

example : (A ∩ Aᶜ) = ∅ := by
  apply subset_antisymm
  · intro a ha
    exfalso
    rcases ha with ⟨ha1, ha2⟩
    rw [mem_compl_iff] at ha2
    contradiction
  · intro a ha
    contradiction

example : (A ∪ B)ᶜ = (Aᶜ ∩ Bᶜ) := by
  apply subset_antisymm
  · intro a ha
    rw [mem_compl_iff] at *
    simp only [Set.mem_union, not_or] at ha
    obtain ⟨ha1, ha2⟩ := ha
    constructor <;>
    rw [mem_compl_iff] <;>
    assumption
  · intro a ha
    rcases ha with ⟨ha1, ha2⟩
    rw [mem_compl_iff] at *
    rw [Set.mem_union, not_or]
    exact { left := ha1, right := ha2 }

example (hy : 0 < y) :
  Tendsto (fun x => (y*x - 1)⁻¹)
  (nhdsWithin (y⁻¹) (Set.Ioo 0 (y⁻¹))) atBot := by
    have h : (fun x => -(y*x - 1)⁻¹) = (fun x => (1 - y*x)⁻¹) := by
      apply funext
      intro x
      field_simp
      refine (div_eq_div_iff_comm (-1) (y * x - 1) 1).mpr ?h.a
      ring
    rw [← tendsto_neg_atTop_iff, h]
    refine Filter.Tendsto.inv_tendsto_zero ?_
    rw [nhdsWithin]
    apply Filter.Tendsto.inf
    · rw [show 0 = 1 - y * y⁻¹ by field_simp]
      apply Filter.Tendsto.sub
      · exact tendsto_const_nhds
      · apply Filter.Tendsto.mul
        · exact tendsto_const_nhds
        · exact fun ⦃U⦄ a => a
    · refine tendsto_principal_principal.mpr ?h₂.a
      intro x hx
      rw [Set.mem_Ioi]
      rcases hx with ⟨_, hx2⟩
      have h' : y*x < y*y⁻¹ := by exact (mul_lt_mul_left hy).mpr hx2
      field_simp at h'
      aesop
