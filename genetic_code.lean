/-
Copyright (c) 2024 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/

import Mathlib

/-
# Genetic code
This file defines 2 functions called `codon` and `anticodon` that match a 3 letter string comprised
  of 4 letters (`U`, `A`, `G`, or `C`) with their respective amino acid.

## Main Definitions
* `codon` : Matches the mRNA codon to the amino acid
* `anticodon` : Matches the tRNA anticodon to the amino acid

## Implementation Details
This file assumes that the reading frame begins at the first nucleotide always.
-/

open Function

/- # The Requirements for a String to be a Triplet or an Amino Acid -/
def rna_triplet := {s : String // s.length == 3 && s.dropWhile "UCGA".toList.contains == ""}
def amino := {x : String // x ∈ ({"Gly", "Ala", "Val", "Leu", "Ile", "Phe", "Trp", "Met", "His",
  "Pro", "Gln", "Asp", "Asn", "Glu", "Arg", "Lys", "Ser", "Cys", "Tyr", "Thr", "STOP"} : Set String
    )}

/- # The Triplet Code # -/
@[match_pattern]
def UUU : rna_triplet := ⟨"UUU", by rfl⟩
@[match_pattern]
def UUC : rna_triplet := ⟨"UUC", by rfl⟩
@[match_pattern]
def UUA : rna_triplet := ⟨"UUA", by rfl⟩
@[match_pattern]
def UUG : rna_triplet := ⟨"UUG", by rfl⟩
@[match_pattern]
def CUU : rna_triplet := ⟨"CUU", by rfl⟩
@[match_pattern]
def CUC : rna_triplet := ⟨"CUC", by rfl⟩
@[match_pattern]
def CUG : rna_triplet := ⟨"CUG", by rfl⟩
@[match_pattern]
def CUA : rna_triplet := ⟨"CUA", by rfl⟩
@[match_pattern]
def AUU : rna_triplet := ⟨"AUU", by rfl⟩
@[match_pattern]
def AUC : rna_triplet := ⟨"AUC", by rfl⟩
@[match_pattern]
def AUA : rna_triplet := ⟨"AUA", by rfl⟩
@[match_pattern]
def AUG : rna_triplet := ⟨"AUG", by rfl⟩
@[match_pattern]
def GUU : rna_triplet := ⟨"GUU", by rfl⟩
@[match_pattern]
def GUC : rna_triplet := ⟨"GUC", by rfl⟩
@[match_pattern]
def GUG : rna_triplet := ⟨"GUG", by rfl⟩
@[match_pattern]
def GUA : rna_triplet := ⟨"GUA", by rfl⟩
@[match_pattern]
def UCU : rna_triplet := ⟨"UCU", by rfl⟩
@[match_pattern]
def UCC : rna_triplet := ⟨"UCC", by rfl⟩
@[match_pattern]
def UCA : rna_triplet := ⟨"UCA", by rfl⟩
@[match_pattern]
def UCG : rna_triplet := ⟨"UCG", by rfl⟩
@[match_pattern]
def CCU : rna_triplet := ⟨"CCU", by rfl⟩
@[match_pattern]
def CCC : rna_triplet := ⟨"CCC", by rfl⟩
@[match_pattern]
def CCG : rna_triplet := ⟨"CCG", by rfl⟩
@[match_pattern]
def CCA : rna_triplet := ⟨"CCA", by rfl⟩
@[match_pattern]
def ACU : rna_triplet := ⟨"ACU", by rfl⟩
@[match_pattern]
def ACC : rna_triplet := ⟨"ACC", by rfl⟩
@[match_pattern]
def ACA : rna_triplet := ⟨"ACA", by rfl⟩
@[match_pattern]
def ACG : rna_triplet := ⟨"ACG", by rfl⟩
@[match_pattern]
def GCU : rna_triplet := ⟨"GCU", by rfl⟩
@[match_pattern]
def GCC : rna_triplet := ⟨"GCC", by rfl⟩
@[match_pattern]
def GCG : rna_triplet := ⟨"GCG", by rfl⟩
@[match_pattern]
def GCA : rna_triplet := ⟨"GCA", by rfl⟩
@[match_pattern]
def UAU : rna_triplet := ⟨"UAU", by rfl⟩
@[match_pattern]
def UAC : rna_triplet := ⟨"UAC", by rfl⟩
@[match_pattern]
def UAA : rna_triplet := ⟨"UAA", by rfl⟩
@[match_pattern]
def UAG : rna_triplet := ⟨"UAG", by rfl⟩
@[match_pattern]
def CAU : rna_triplet := ⟨"CAU", by rfl⟩
@[match_pattern]
def CAC : rna_triplet := ⟨"CAC", by rfl⟩
@[match_pattern]
def CAG : rna_triplet := ⟨"CAG", by rfl⟩
@[match_pattern]
def CAA : rna_triplet := ⟨"CAA", by rfl⟩
@[match_pattern]
def AAU : rna_triplet := ⟨"AAU", by rfl⟩
@[match_pattern]
def AAC : rna_triplet := ⟨"AAC", by rfl⟩
@[match_pattern]
def AAA : rna_triplet := ⟨"AAA", by rfl⟩
@[match_pattern]
def AAG : rna_triplet := ⟨"AAG", by rfl⟩
@[match_pattern]
def GAU : rna_triplet := ⟨"GAU", by rfl⟩
@[match_pattern]
def GAC : rna_triplet := ⟨"GAC", by rfl⟩
@[match_pattern]
def GAG : rna_triplet := ⟨"GAG", by rfl⟩
@[match_pattern]
def GAA : rna_triplet := ⟨"GAA", by rfl⟩
@[match_pattern]
def UGU : rna_triplet := ⟨"UGU", by rfl⟩
@[match_pattern]
def UGC : rna_triplet := ⟨"UGC", by rfl⟩
@[match_pattern]
def UGA : rna_triplet := ⟨"UGA", by rfl⟩
@[match_pattern]
def UGG : rna_triplet := ⟨"UGG", by rfl⟩
@[match_pattern]
def CGU : rna_triplet := ⟨"CGU", by rfl⟩
@[match_pattern]
def CGC : rna_triplet := ⟨"CGC", by rfl⟩
@[match_pattern]
def CGG : rna_triplet := ⟨"CGG", by rfl⟩
@[match_pattern]
def CGA : rna_triplet := ⟨"CGA", by rfl⟩
@[match_pattern]
def AGU : rna_triplet := ⟨"AGU", by rfl⟩
@[match_pattern]
def AGC : rna_triplet := ⟨"AGC", by rfl⟩
@[match_pattern]
def AGA : rna_triplet := ⟨"AGA", by rfl⟩
@[match_pattern]
def AGG : rna_triplet := ⟨"AGG", by rfl⟩
@[match_pattern]
def GGU : rna_triplet := ⟨"GGU", by rfl⟩
@[match_pattern]
def GGC : rna_triplet := ⟨"GGC", by rfl⟩
@[match_pattern]
def GGG : rna_triplet := ⟨"GGG", by rfl⟩
@[match_pattern]
def GGA : rna_triplet := ⟨"GGA", by rfl⟩

/- # The Amino Acids # -/
def Phe : amino := ⟨"Phe", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Gly : amino := ⟨"Gly", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Ala : amino := ⟨"Ala", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Val : amino := ⟨"Val", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Leu : amino := ⟨"Leu", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Ile : amino := ⟨"Ile", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Gln : amino := ⟨"Gln", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Asn : amino := ⟨"Asn", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Asp : amino := ⟨"Asp", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Glu : amino := ⟨"Glu", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Arg : amino := ⟨"Arg", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Lys : amino := ⟨"Lys", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Trp : amino := ⟨"Trp", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Tyr : amino := ⟨"Tyr", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Met : amino := ⟨"Met", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Ser : amino := ⟨"Ser", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def His : amino := ⟨"His", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Pro : amino := ⟨"Pro", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Thr : amino := ⟨"Thr", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def Cys : amino := ⟨"Cys", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩
def STOP : amino := ⟨"STOP", by simp only [Set.mem_insert_iff, String.reduceEq,
  Set.mem_singleton_iff, or_self, or_false, or_true]⟩

/- # The Codon Function #
  Matches a codon with its corresponding amino acid during Translation
-/
def codon (s : rna_triplet) :=
  match s with
  | UUU => Phe
  | UUC => Phe
  | UUA => Leu
  | UUG => Leu
  | CUU => Leu
  | CUC => Leu
  | CUA => Leu
  | CUG => Leu
  | AUU => Ile
  | AUC => Ile
  | AUG => Met
  | GUU => Val
  | GUC => Val
  | GUA => Val
  | GUG => Val
  | UCU => Ser
  | UCC => Ser
  | UCA => Ser
  | UCG => Ser
  | CCU => Pro
  | CCC => Pro
  | CCA => Pro
  | CCG => Pro
  | ACU => Thr
  | ACC => Thr
  | ACA => Thr
  | ACG => Thr
  | GCU => Ala
  | GCC => Ala
  | GCA => Ala
  | GCG => Ala
  | UAU => Tyr
  | UAC => Tyr
  | UAA => STOP
  | UAG => STOP
  | CAU => His
  | CAC => His
  | CAA => Gln
  | CAG => Gln
  | AAU => Asn
  | AAC => Asn
  | AAA => Lys
  | AAG => Lys
  | GAU => Asp
  | GAC => Asp
  | GAA => Glu
  | GAG => Glu
  | UGU => Cys
  | UGC => Cys
  | UGA => STOP
  | UGG => Trp
  | CGU => Arg
  | CGC => Arg
  | CGA => Arg
  | CGG => Arg
  | AGU => Ser
  | AGC => Ser
  | AGA => Arg
  | AGG => Arg
  | GGU => Gly
  | GGC => Gly
  | GGA => Gly
  | GGG => Gly
  | _ => STOP

#eval codon GGG

/- # Proofs # -/
def redundant (f : α → β) : Prop := ¬ Injective f

theorem all_amino (YYY : amino) : YYY = Gly ∨ YYY = Ala ∨ YYY = Val ∨ YYY = Leu ∨ YYY =
  Ile ∨ YYY = Phe ∨ YYY = Trp ∨ YYY = Met ∨ YYY = His ∨ YYY = Pro ∨ YYY = Gln ∨ YYY
  = Asp ∨ YYY = Asn ∨ YYY = Glu ∨ YYY = Arg ∨ YYY = Lys ∨ YYY = Ser ∨ YYY = Cys ∨ YYY
  = Tyr ∨ YYY = Thr ∨ YYY = STOP := by
  obtain ⟨_, h⟩ := YYY
  simpa [Ala, Arg, Asn, Asp, Cys, Gln, Glu, Gly, His, Ile, Leu, Lys, Met, Phe, Pro, Ser, Thr,
    Trp, Tyr, Val, STOP, amino] using h

theorem not_injective_codon : ¬ Injective codon := by
  simp only [Injective, not_forall, Classical.not_imp, exists_prop]
  use UUU, UUC
  constructor
  · rfl
  · intro h
    simpa [UUU, UUC] using congrArg Subtype.val h

theorem redundant_codon : redundant codon := by
  dsimp only [redundant]
  exact not_injective_codon

theorem surjective_codon : Surjective codon := by
  simp only [Surjective]
  intro YYY
  have hy := all_amino YYY
  rcases hy with (h | (h | (h | (h | (h | (h | (h | (h | (h | (h | (h | (h | (h | (h | (h | (h |
    (h | (h | (h | (h | h))))))))))))))))))))
  repeat (first | rw [h] | use GGU; rfl | use GCU; rfl | use GUU; rfl | use UUA; rfl | use AUU; rfl)
  repeat (first | rw [h] | use UUU; rfl | use UGG; rfl | use AUG; rfl | use CAU; rfl | use CCU; rfl)
  repeat (first | rw [h] | use CAA; rfl | use AAU; rfl | use GAU; rfl | use GAA; rfl | use CGU; rfl)
  repeat (first | rw [h] | use AAA; rfl | use UCC; rfl | use UGU; rfl | use UAU; rfl | use ACU; rfl)
  use UGA
  rfl

def genetic_code (L : List rna_triplet) : List amino :=
  match L with
  | [] => []
  | y :: ys => [codon y] ++ genetic_code ys

#eval genetic_code [UUU, UUA, GGC, CCA, CCC, UGA, UGG, UGC, CCC, CCA]

theorem not_injective_genetic_code : ¬ Injective genetic_code := by
  simp only [Injective, not_forall, exists_prop]
  use [ACU, ACC], [ACC, ACU]
  constructor
  · rfl
  · simp only [List.cons.injEq, and_true, not_and]
    intro h
    simpa [ACC, ACU] using congrArg Subtype.val h

theorem redundant_genetic_code : redundant genetic_code := by
  dsimp only [redundant]
  exact not_injective_genetic_code

/-
theorem all_codon (XXX : rna_triplet) : XXX = ⟨"AAA", by rfl⟩ ∨ XXX = ⟨"AAU", by rfl⟩ ∨ XXX = ⟨
  "AAG", by rfl⟩ ∨ XXX = ⟨"AAC", by rfl⟩ ∨ XXX = ⟨"AUA", by rfl⟩ ∨ XXX = ⟨"AUU", by rfl⟩ ∨ XXX =
  ⟨"AUG", by rfl⟩ ∨ XXX = ⟨"AUC", by rfl⟩ ∨ XXX = ⟨"AGA", by rfl⟩ ∨ XXX = ⟨"AGU", by rfl⟩ ∨ XXX =
  ⟨"AGG", by rfl⟩ ∨ XXX = ⟨"AGC", by rfl⟩ ∨ XXX = ⟨"ACA", by rfl⟩ ∨ XXX = ⟨"ACU", by rfl⟩ ∨ XXX =
  ⟨"ACG", by rfl⟩ ∨ XXX = ⟨"ACC", by rfl⟩ ∨ XXX = ⟨"UAA", by rfl⟩ ∨ XXX = ⟨"UAU", by rfl⟩ ∨ XXX =
  ⟨"UAG", by rfl⟩ ∨ XXX = ⟨"UAC", by rfl⟩ ∨ XXX = ⟨"UUA", by rfl⟩ ∨ XXX = ⟨"UUU", by rfl⟩ ∨ XXX =
  ⟨"UUG", by rfl⟩ ∨ XXX = ⟨"UUC", by rfl⟩ ∨ XXX = ⟨"UGA", by rfl⟩ ∨ XXX = ⟨"UGU", by rfl⟩ ∨ XXX =
  ⟨"UGG", by rfl⟩ ∨ XXX = ⟨"UGC", by rfl⟩ ∨ XXX = ⟨"UCA", by rfl⟩ ∨ XXX = ⟨"UCU", by rfl⟩ ∨ XXX =
  ⟨"UCG", by rfl⟩ ∨ XXX = ⟨"UCC", by rfl⟩ ∨ XXX = ⟨"GAA", by rfl⟩ ∨ XXX = ⟨"GAU", by rfl⟩ ∨ XXX =
  ⟨"GAG", by rfl⟩ ∨ XXX = ⟨"GAC", by rfl⟩ ∨ XXX = ⟨"GUA", by rfl⟩ ∨ XXX = ⟨"GUU", by rfl⟩ ∨ XXX =
  ⟨"GUG", by rfl⟩ ∨ XXX = ⟨"GUC", by rfl⟩ ∨ XXX = ⟨"GGA", by rfl⟩ ∨ XXX = ⟨"GGU", by rfl⟩ ∨ XXX =
  ⟨"GGG", by rfl⟩ ∨ XXX = ⟨"GGC", by rfl⟩ ∨ XXX = ⟨"GCA", by rfl⟩ ∨ XXX = ⟨"GCU", by rfl⟩ ∨ XXX =
  ⟨"GCG", by rfl⟩ ∨ XXX = ⟨"GCC", by rfl⟩ ∨ XXX = ⟨"CAA", by rfl⟩ ∨ XXX = ⟨"CAU", by rfl⟩ ∨ XXX =
  ⟨"CAG", by rfl⟩ ∨ XXX = ⟨"CAC", by rfl⟩ ∨ XXX = ⟨"CUA", by rfl⟩ ∨ XXX = ⟨"CUU", by rfl⟩ ∨ XXX =
  ⟨"CUG", by rfl⟩ ∨ XXX = ⟨"CUC", by rfl⟩ ∨ XXX = ⟨"CGA", by rfl⟩ ∨ XXX = ⟨"CGU", by rfl⟩ ∨ XXX =
  ⟨"CGG", by rfl⟩ ∨ XXX = ⟨"CGC", by rfl⟩ ∨ XXX = ⟨"CCA", by rfl⟩ ∨ XXX = ⟨"CCU", by rfl⟩ ∨ XXX =
  ⟨"CCG", by rfl⟩ ∨ XXX = ⟨"CCC", by rfl⟩
:= by
    obtain ⟨h, property⟩ := XXX
    left
    sorry
-/

def genomic_alignment (L₁ : List rna_triplet) (L₂ : List rna_triplet) : ℝ := by
  sorry
