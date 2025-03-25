/-
Authors: Colin Jones
Date: 03/24/2025
Description: Contains a function that allows the user to convert a coding strand of DNA into a
  sequence of RNA or amino acids. Proves the injectivity of mapping DNA to RNA and the redundancy
  (non-injectivity) of DNA and RNA to amino acid.
-/

import Mathlib

/-
# Genetic code
This file defines 2 functions called `codon` and `anticodon` that match a 3 letter string comprised
  of 4 letters (`U`, `A`, `G`, or `C`) with their respective amino acid.

## Main Definitions
* `dna_to_rna`: Converts a coding strand of DNA into RNA
* `rna_to_amino`: Takes a list of RNA triplets and converts them into a list of amino acids
* `dna_to_rna`: Converts a coding strand of DNA into a sequence of amino acids

## Implementation Details
This file assumes that the reading frame begins at the first nucleotide always and all lists are
  5' → 3'. The function `dna_to_rna` takes the coding strand as an input, so it is 'read' backwards
  from the 3' → 5' direction e.g. `[A, G, T]` becomes `[A, C, U]`. Proof has to be given
  that the input is a valid DNA base or contains DNA bases in the functions: `dna_to_rna_singlet`,
  `dna_to_rna`, and `dna_to_amino`. To prove this is true, include `(by aesop)` at the end of the
  `#eval` function like this: `#eval dna_to_rna [A, G, T] (by aesop) -- will output [A, C, U]`.
-/

open Function Classical

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
def dna_to_rna_singlet (n : NucBase) (valid : n.isDNABase) :=
  match n with
  | T => A
  | A => U
  | G => C
  | C => G

def dna_to_rna (s : List NucBase) (valid : ∀ n ∈ s, n.isDNABase) : List NucBase :=
  (s.reverse).pmap dna_to_rna_singlet (by simp only [List.mem_reverse]; exact valid)


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

def rna_to_amino (s : List (List NucBase)) : List AminoAcid :=
  match s with
  | [] => []
  | y :: ys => [rna_to_amino_single_triplet y] ++ rna_to_amino ys


/- ### Main Function ###
  dna_to_amino: Takes a list of DNA nucleic acids and converts them into a sequence of amino acids
-/
def dna_to_amino (s : List NucBase) (valid : ∀ n ∈ s, n.isDNABase) : List AminoAcid :=
  (dna_to_rna s (by aesop)).toChunks 3 |> rna_to_amino


/- # Proofs # -/
theorem injective_dna_to_rna_singlet :
    Injective (fun n : {x // NucBase.isDNABase x} ↦ dna_to_rna_singlet n n.prop) := by
  rintro ⟨n, hn⟩ ⟨m, hm⟩
  cases n <;> cases m <;>
  any_goals simp [isDNABase] at hn hm
  all_goals simp [dna_to_rna_singlet]

theorem redundant_genetic_code :
    Redundant (fun s : {x : List NucBase // ∀ n ∈ x, n.isDNABase} ↦ dna_to_amino s s.prop)
    := by
  simp only [Redundant, Injective, not_forall]
  use ⟨[A, A, A], by decide⟩, ⟨[G, A, A], by decide⟩
  simp only [Subtype.mk.injEq, List.cons.injEq, reduceCtorEq, and_true, not_false_eq_true,
    exists_prop]
  rfl

theorem redundant_rna_to_amino : Redundant rna_to_amino := by
  simp only [Redundant, Injective, not_forall]
  use [[U, U, U]], [[U, U, C]]
  simp only [List.cons.injEq, reduceCtorEq, and_true, not_false_eq_true, exists_prop]
  exact ⟨rfl, of_decide_eq_false rfl⟩
