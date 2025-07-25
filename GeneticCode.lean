/-
Authors: Colin Jones
Last Updated: 07/25/2025
Description: Contains a function that allows the user to convert a coding strand of DNA into a
  sequence of RNA or amino acids. Proves the injectivity of mapping DNA to RNA and the redundancy
  (non-injectivity) of DNA and RNA to amino acid. Includes brief exploration of point mutations.
-/

import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.List.Basic

/-
# Genetic code
This file defines 2 functions called `codon` and `anticodon` that match a 3 letter string comprised
  of 4 letters (`U`, `A`, `G`, or `C`) with their respective amino acid.

## Main Definitions
* `Redundant`: Not injective, not one-to-one

## Main Functions
* `dna_to_rna_template`: Converts a coding strand of DNA into RNA assuming the strand is template
* `dna_to_rna_coding`: Converts a coding strand of DNA into RNA assuming the strand is coding
* `rna_to_amino`: Takes a list of RNA triplets and converts them into a list of amino acids
* `dna_to_rna_template`: Converts a coding strand of DNA into a sequence of amino acids assuming
    template strand is the input
* `dna_to_rna_coding`: Converts a coding strand of DNA into a sequence of amino acids assuming
    coding strand is input
* `dna_to_amino_template`: Converts a template strand of DNA into its corresponding peptide chain
* `dna_to_amino_coding`: Converts a template strand of DNA into its corresponding peptide chain

## Main Proofs
* `template_coding_equivalence`: `dna_to_rna_template` applied to a list is equivalent to
    `dna_to_rna` applied to that list reversed
* `length_conservation`: The length of the list is equal to the length of the output of
    `dna_to_rna_template` applied to that list
* `injective_dna_to_rna_template`: The function `dna_to_rna_template` is injective or one-to-one
* `redundant_rna_to_amino`: The function `rna_to_amino` is redundant or not injective
* `redundant_genetic_code`: The function `dna_to_amino_template` representing the genetic code is
    redundant

## Implementation Details
This file assumes that the reading frame begins at the first nucleotide always and all lists are
  5' → 3'. The function `dna_to_rna_template` takes the template strand as an input, so it is
  'read' backwards from the 3' → 5' direction e.g. `[A, G, T]` becomes `[A, C, U]`. Proof has to be
  given that the input is a valid DNA base or contains DNA bases in the functions:
  `dna_to_rna_singlet`, `dna_to_rna_template`, `dna_to_rna_coding`, `dna_to_amino_template`, and
  `dna_to_amino_coding`. To prove this is true, include `(by aesop)` at the end of the `#eval`
  function like this: `#eval dna_to_rna_template [A, G, T] (by aesop)`. That particular input will
  output `[A, C, U]` in the Lean InfoView.
-/

open Function Classical List

variable (n : NucBase) (s : List NucBase) (i : ℕ)

/- # Definition of Nucleotide Base #
  U := Uracil
  A := Adenosine
  G := Guanosine
  C := Cytosine
  T := Thymine
-/
inductive NucBase
  | U | A | G | C | T
  deriving DecidableEq, Repr
open NucBase


/- # Definition of Amino Acid #
  Each amino acid is abbreviated by their single-letter abbreviation except for the stop codon
  which is represented as `STOP`.
-/
inductive AminoAcid
  | G | D | E | V | K | R | H | P | Q | F | T | W | Y | M | S | L | I | A | C | N | STOP
  deriving DecidableEq, Repr


/- # General Definitions # -/
def NucBase.isRNABase : Bool := n matches U | A | G | C

def NucBase.isDNABase : Bool := n matches T | A | G | C

def Redundant {α β} (f : α → β) : Prop := ¬ Injective f


/- # DNA Function Definitions # -/
def T_to_U (n : NucBase) (_ : n.isDNABase) :=
  if n = T then U else n

def dna_to_rna_singlet (n : NucBase) (hn : n.isDNABase) :=
  match n with
  | T => A
  | A => U
  | G => C
  | C => G

def dna_to_dna_singlet (n : NucBase) (hn : n.isDNABase) :=
  match n with
  | T => A
  | A => T
  | G => C
  | C => G

def dna_to_rna_template (hs : ∀ n ∈ s, n.isDNABase) : List NucBase :=
  (s.reverse).pmap dna_to_rna_singlet (by aesop)

def dna_to_rna_coding (_ : ∀ n ∈ s, n.isDNABase) : List NucBase :=
  s.pmap T_to_U (by aesop)

def dna_replication (hs : ∀ n ∈ s, n.isDNABase) : List NucBase :=
  s.pmap dna_to_dna_singlet hs


/- # RNA Function Definitions # -/
def rna_to_amino_single_triplet (s : List NucBase) : AminoAcid :=
  match s with
  | [U, U, U] => AminoAcid.F
  | [U, U, C] => AminoAcid.F
  | [U, U, A] => AminoAcid.L
  | [U, U, G] => AminoAcid.L
  | [C, U, U] => AminoAcid.L
  | [C, U, C] => AminoAcid.L
  | [C, U, A] => AminoAcid.L
  | [C, U, G] => AminoAcid.L
  | [A, U, U] => AminoAcid.I
  | [A, U, C] => AminoAcid.I
  | [A, U, A] => AminoAcid.I
  | [A, U, G] => AminoAcid.M
  | [G, U, U] => AminoAcid.V
  | [G, U, C] => AminoAcid.V
  | [G, U, A] => AminoAcid.V
  | [G, U, G] => AminoAcid.V
  | [U, C, U] => AminoAcid.S
  | [U, C, C] => AminoAcid.S
  | [U, C, A] => AminoAcid.S
  | [U, C, G] => AminoAcid.S
  | [C, C, U] => AminoAcid.P
  | [C, C, C] => AminoAcid.P
  | [C, C, A] => AminoAcid.P
  | [C, C, G] => AminoAcid.P
  | [A, C, U] => AminoAcid.T
  | [A, C, C] => AminoAcid.T
  | [A, C, A] => AminoAcid.T
  | [A, C, G] => AminoAcid.T
  | [G, C, U] => AminoAcid.A
  | [G, C, C] => AminoAcid.A
  | [G, C, A] => AminoAcid.A
  | [G, C, G] => AminoAcid.A
  | [U, A, U] => AminoAcid.Y
  | [U, A, C] => AminoAcid.Y
  | [U, A, A] => AminoAcid.STOP
  | [U, A, G] => AminoAcid.STOP
  | [C, A, U] => AminoAcid.H
  | [C, A, C] => AminoAcid.H
  | [C, A, A] => AminoAcid.Q
  | [C, A, G] => AminoAcid.Q
  | [A, A, U] => AminoAcid.N
  | [A, A, C] => AminoAcid.N
  | [A, A, A] => AminoAcid.K
  | [A, A, G] => AminoAcid.K
  | [G, A, U] => AminoAcid.D
  | [G, A, C] => AminoAcid.D
  | [G, A, A] => AminoAcid.E
  | [G, A, G] => AminoAcid.E
  | [U, G, U] => AminoAcid.C
  | [U, G, C] => AminoAcid.C
  | [U, G, A] => AminoAcid.STOP
  | [U, G, G] => AminoAcid.W
  | [C, G, U] => AminoAcid.R
  | [C, G, C] => AminoAcid.R
  | [C, G, A] => AminoAcid.R
  | [C, G, G] => AminoAcid.R
  | [A, G, U] => AminoAcid.S
  | [A, G, C] => AminoAcid.S
  | [A, G, A] => AminoAcid.R
  | [A, G, G] => AminoAcid.R
  | [G, G, U] => AminoAcid.G
  | [G, G, C] => AminoAcid.G
  | [G, G, A] => AminoAcid.G
  | [G, G, G] => AminoAcid.G
  | _ => AminoAcid.STOP

def rna_to_amino (L : List (List NucBase)) : List AminoAcid :=
  match L with
  | [] => []
  | y :: ys => [rna_to_amino_single_triplet y] ++ rna_to_amino ys

def rna_to_dna_singlet (n : NucBase) (hn : n.isRNABase) :=
  match n with
  | U => A
  | A => T
  | G => C
  | C => G

def rna_to_dna (hs : ∀ n ∈ s, n.isRNABase) : List NucBase :=
  s.pmap rna_to_dna_singlet hs


/- ### Main Functions ###
  dna_to_amino: Takes a list of DNA nucleic acids and converts them into a sequence of amino acids
-/
def dna_to_amino_template (hs : ∀ n ∈ s, n.isDNABase) : List AminoAcid :=
  (dna_to_rna_template s hs).toChunks 3 |> rna_to_amino

def dna_to_amino_coding (hs : ∀ n ∈ s, n.isDNABase) : List AminoAcid :=
  (dna_to_rna_coding s hs).toChunks 3 |> rna_to_amino


/- # Mutations # -/
def point_mutation := s.set i n


/- # Proofs # -/
theorem length_conservation (hs : ∀ n ∈ s, n.isDNABase = True) :
    s.length = (dna_to_rna_template s hs).length ∧ s.length = (dna_to_rna_coding s hs).length := by
  constructor <;>
  · induction s
    · rfl
    · simp only [mem_cons, or_true, decide_true, implies_true, forall_true_left, forall_eq_or_imp,
        length_cons, map_cons, length_map, Nat.add_left_cancel_iff, dna_to_rna_coding,
        dna_to_rna_template, reverse_cons, pmap_append, pmap_reverse, pmap_cons, pmap_nil,
        length_append, length_reverse, length_pmap, length_nil, zero_add]

lemma injective_dna_to_rna_singlet :
    Injective (fun n : {x // NucBase.isDNABase x} ↦ dna_to_rna_singlet n n.prop) := by
  rintro ⟨n, hn⟩ ⟨m, hm⟩
  cases n <;> cases m <;>
  any_goals simp [isDNABase] at hn hm
  all_goals simp [dna_to_rna_singlet]

lemma singlet_iff (n₁ n₂ : {x // NucBase.isDNABase x}) :
    dna_to_rna_singlet n₁ n₁.prop = dna_to_rna_singlet n₂ n₂.prop ↔ n₁ = n₂ := by
  obtain ⟨n₁, hn₁⟩ := n₁
  obtain ⟨n₂, hn₂⟩ := n₂
  constructor <;> simp only [Subtype.mk.injEq]
  · have h' := injective_dna_to_rna_singlet
    simp only [Injective, Subtype.forall, Subtype.mk.injEq] at h'
    apply h' <;> assumption
  · intro h
    congr

theorem injective_dna_to_rna_template :
    Injective (fun s : {x : List NucBase // ∀ n ∈ x, n.isDNABase} ↦ dna_to_rna_template s s.prop)
    := by
  rintro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩
  simp only [Subtype.mk.injEq]
  intro h
  have hL : s₁.length = s₂.length := by
    rw [(length_conservation s₁ hs₁).1, (length_conservation s₂ hs₂).1]
    exact congrArg length h
  apply Array.ext.extAux s₁ s₂ hL
  intro i hi₁ hi₂
  have hi₁' : i < s₁.reverse.length := by simp_all only [length_reverse]
  have hi₂' : i < s₂.reverse.length := by simp_all only [length_reverse]
  unfold dna_to_rna_template at h
  rw [ext_get_iff] at h
  obtain ⟨h1, h2⟩ := h
  simp only [length_pmap, get_eq_getElem, getElem_pmap, forall_true_left] at h2
  have hn := h2 i (by aesop) (by aesop)
  have hi := singlet_iff
  simp only [Subtype.forall, Subtype.mk.injEq] at hi
  have hj : s₁.reverse[i] = s₂.reverse[i] := by simp_all only [pmap_reverse, length_reverse,
    length_pmap, getElem_reverse, getElem_mem]
  apply getElem_of_eq
  have hj' := Array.ext.extAux s₁.reverse s₂.reverse (by aesop) (by aesop)
  simp_all only [pmap_reverse, length_reverse, length_pmap, getElem_reverse, imp_self,
    implies_true, reverse_inj]

lemma injective_T_to_U : Injective (fun n : {x // NucBase.isDNABase x} ↦ T_to_U n n.prop) := by
  rintro ⟨n, hn⟩ ⟨m, hm⟩
  cases n <;> cases m <;>
  repeat (first | intro h; simp_all | contradiction)

theorem injective_dna_to_rna_coding :
    Injective (fun s : {x : List NucBase // ∀ n ∈ x, n.isDNABase} ↦ dna_to_rna_coding s s.prop)
    := by
  rintro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩
  simp only [Subtype.mk.injEq]
  intro h
  have hL : s₁.length = s₂.length := by
    rw [(length_conservation s₁ hs₁).2, (length_conservation s₂ hs₂).2]
    exact congrArg length h
  apply Array.ext.extAux s₁ s₂ hL
  intro i hi₁ hi₂
  unfold dna_to_rna_coding at h
  rw [ext_get_iff] at h
  obtain ⟨h1, h2⟩ := h
  simp only [length_pmap, get_eq_getElem, getElem_pmap, forall_true_left] at h2
  have hn := by apply h2 i hi₁ hi₂
  have hi := injective_T_to_U
  unfold Injective at hi
  simp only [length_pmap, forall_true_left, Subtype.forall, Subtype.mk.injEq, getElem_mem] at hi
  apply hi
  exact hn
  repeat simp_all only [length_pmap, getElem_mem, forall_true_left]

theorem redundant_rna_to_amino : Redundant rna_to_amino := by
  simp only [Redundant, Injective, not_forall]
  use [[U, U, U]], [[U, U, C]]
  simp only [cons.injEq, reduceCtorEq, and_true, not_false_eq_true, exists_prop]
  exact ⟨rfl, of_decide_eq_false rfl⟩

theorem redundant_genetic_code_template :
    Redundant (fun s : {x : List NucBase // ∀ n ∈ x, n.isDNABase} ↦ dna_to_amino_template s s.prop)
    := by
  simp only [Redundant, Injective, not_forall]
  use ⟨[A, A, A], by decide⟩, ⟨[G, A, A], by decide⟩
  simp only [Subtype.mk.injEq, cons.injEq, reduceCtorEq, and_true, not_false_eq_true,
    exists_prop]
  rfl

theorem redundant_genetic_code_coding :
  Redundant (fun s : {x : List NucBase // ∀ n ∈ x, n.isDNABase} ↦ dna_to_amino_coding s s.prop)
    := by
  simp only [Redundant, Injective, not_forall]
  use ⟨[A, A, A], by decide⟩, ⟨[A, A, G], by decide⟩
  simp only [Subtype.mk.injEq, cons.injEq, reduceCtorEq, and_true, and_false, not_false_eq_true,
    exists_prop]
  rfl
