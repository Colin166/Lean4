/-
Authors: Colin Jones
Last Updated: 06/10/2025
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
  `dna_to_rna_singlet`, `dna_to_rna_template`, and `dna_to_amino`. To prove this is true, include
  `(by aesop)` at the end of the `#eval` function like this: `#eval dna_to_rna_template [A, G, T]
  (by aesop). That particular input will output [A, C, U]` in the Lean InfoView.
-/

open Function Classical List

variable (n : NucBase) (s : List NucBase)

/- # Definition of Nucleotide Base #
  U := Uracil
  A := Adenosine
  G := Guanosine
  C := Cytosine
  T := Thymine
-/
inductive NucBase
  | U | A | G | C | T
open NucBase
deriving instance Repr for NucBase


/- # Definition of Amino Acid #
  Each amino acid is abbreviated by their single-letter abbreviation except for the stop codon
  which is represented as `STOP`.
-/
inductive AminoAcid
  | G | D | E | V | K | R | H | P | Q | F | T | W | Y | M | S | L | I | A | C | N | STOP
deriving instance Repr for AminoAcid


/- # General Definitions # -/
def NucBase.isRNABase (b : NucBase) : Bool := b matches U | A | G | C

def NucBase.isDNABase (b : NucBase) : Bool := b matches T | A | G | C

def Redundant (f : α → β) : Prop := ¬ Injective f


/- # DNA Function Definitions # -/
def dna_to_rna_singlet (n : NucBase) (hn : n.isDNABase) :=
  match n with
  | T => A
  | A => U
  | G => C
  | C => G

def dna_to_rna_template (hs : ∀ n ∈ s, n.isDNABase) : List NucBase :=
  (s.reverse).pmap dna_to_rna_singlet (by aesop)

def dna_to_rna_coding (hs : ∀ n ∈ s, n.isDNABase) : List NucBase :=
  s.pmap dna_to_rna_singlet hs


/- # RNA Function Definitions # -/
def rna_to_amino_single_triplet : AminoAcid :=
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


/- ### Main Function ###
  dna_to_amino: Takes a list of DNA nucleic acids and converts them into a sequence of amino acids
-/
def dna_to_amino_template (hs : ∀ n ∈ s, n.isDNABase) : List AminoAcid :=
  (dna_to_rna_template s hs).toChunks 3 |> rna_to_amino

def dna_to_amino_coding (hs : ∀ n ∈ s, n.isDNABase) : List AminoAcid :=
  (dna_to_rna_coding s hs).toChunks 3 |> rna_to_amino


/- # Proofs # -/
lemma template_coding_toRNA_equivalence (hs : ∀ n ∈ s, n.isDNABase) :
    dna_to_rna_template s.reverse (by aesop) = dna_to_rna_coding s hs ∧
    dna_to_rna_template s hs = dna_to_rna_coding s.reverse (by aesop) := by
  constructor
  · unfold dna_to_rna_template dna_to_rna_coding
    congr
    rw [reverse_reverse s]
  · exact rfl

theorem template_coding_toAmino_equivalence (hs : ∀ n ∈ s, n.isDNABase) :
    dna_to_amino_template s.reverse (by aesop) = dna_to_amino_coding s hs ∧
    dna_to_amino_template s (hs) = dna_to_amino_coding s.reverse (by aesop) := by
  unfold dna_to_amino_template dna_to_amino_coding
  rw [(template_coding_toRNA_equivalence s hs).1, (template_coding_toRNA_equivalence s hs).2]
  exact ⟨rfl, rfl⟩

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

theorem length_conservation (hs : ∀ n ∈ s, n.isDNABase = True) :
    s.length = (dna_to_rna_template s hs).length := by
  induction s
  · rfl
  · simp only [length_cons, dna_to_rna_template, reverse_cons, pmap_append, pmap_reverse,
      pmap_cons, pmap_nil, length_append, length_reverse, length_pmap,
      length_cons, length_nil, zero_add]

lemma length_equivalence (s₁ s₂ : List NucBase) (hs₁ : ∀ n₁ ∈ s₁, n₁.isDNABase = True)
    (hs₂ : ∀ n₂ ∈ s₂, n₂.isDNABase = True) :
    s₁.length = s₂.length ↔ (dna_to_rna_template s₁ hs₁).length =
      (dna_to_rna_template s₂ hs₂).length := by
  apply Iff.intro <;> intro h
  · rw [← length_conservation s₁, ← length_conservation s₂, h]
  · rw [length_conservation s₁, length_conservation s₂, h]

theorem injective_dna_to_rna_template :
    Injective (fun s : {x : List NucBase // ∀ n ∈ x, n.isDNABase} ↦ dna_to_rna_template s s.prop)
    := by
  rintro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩
  simp only [Subtype.mk.injEq]
  contrapose
  intro h
  by_cases hL : s₁.length = s₂.length
  · simp only [ext_get_iff, get_eq_getElem, not_and, not_forall] at h
    have ⟨x, hx₁, hx₂, hx⟩ := h hL
    have hi := singlet_iff ⟨s₁[x], (hs₁ s₁[x] (getElem_mem hx₁))⟩ ⟨s₂[x], (hs₂ s₂[x]
      (getElem_mem hx₂))⟩
    have h₀ : dna_to_rna_singlet s₁[x] (hs₁ s₁[x] (getElem_mem hx₁)) ≠ dna_to_rna_singlet s₂[x]
        (hs₂ s₂[x] (getElem_mem hx₂)) := by
      intro ht
      have ht₀ : s₁[x] = s₂[x] := by aesop
      contradiction
    have hj₁ : (pmap dna_to_rna_singlet s₁ hs₁).length =
        (pmap dna_to_rna_singlet s₁.reverse (by aesop)).length := by
      simp only [exists_idem, forall_const, Subtype.mk.injEq, ne_eq, length_pmap,
        pmap_reverse, length_reverse]
    have hj₂ : (pmap dna_to_rna_singlet s₂ hs₂).length =
        (pmap dna_to_rna_singlet s₂.reverse (by aesop)).length := by
      simp only [length_pmap, pmap_reverse, length_reverse]
    rw [length_conservation s₁] at hx₁
    unfold dna_to_rna_template at hx₁
    rw [← hj₁] at hx₁
    rw [length_conservation s₂] at hx₂
    unfold dna_to_rna_template at hx₂
    rw [← hj₂] at hx₂
    simp only [Subtype.mk.injEq] at hi
    intro hc
    simp only [dna_to_rna_template, pmap_reverse, reverse_inj] at hc
    rw [ext_get_iff] at hc
    obtain ⟨hc₁, hc₂⟩ := hc
    have hc₃ := hc₂ x hx₁ hx₂
    simp only [id_eq, eq_mpr_eq_cast, get_eq_getElem, getElem_pmap] at hc₃
    contradiction
    all_goals assumption
  · intro h
    have h₁ := congrArg length h
    have h₂ : (dna_to_rna_template s₁ hs₁).length ≠ (dna_to_rna_template s₂ hs₂).length := by
      rw [← length_conservation s₁, ← length_conservation s₂]
      exact hL
    contradiction

theorem redundant_rna_to_amino : Redundant rna_to_amino := by
  simp only [Redundant, Injective, not_forall]
  use [[U, U, U]], [[U, U, C]]
  simp only [cons.injEq, reduceCtorEq, and_true, not_false_eq_true, exists_prop]
  exact ⟨rfl, of_decide_eq_false rfl⟩

theorem redundant_genetic_code :
    Redundant (fun s : {x : List NucBase // ∀ n ∈ x, n.isDNABase} ↦ dna_to_amino_template s s.prop)
    := by
  simp only [Redundant, Injective, not_forall]
  use ⟨[A, A, A], by decide⟩, ⟨[G, A, A], by decide⟩
  simp only [Subtype.mk.injEq, cons.injEq, reduceCtorEq, and_true, not_false_eq_true,
    exists_prop]
  rfl
