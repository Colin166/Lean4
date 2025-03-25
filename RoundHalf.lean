/-
Copyright (c) 2024 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
import Mathlib.Algebra.Order.Floor

/-!
# Two new `round` theorems
This file documents the two theorems I added to Mathlib in the file floor.lean.

## Theorems
Let `x` be an element of a Linear Ordered Field and a Floor Ring then
* `sub_half_lt_round` : `x - 1 / 2 < round x`
* `round_le_add_half` : `round x ≤ x + 1 / 2`

-/

variable [LinearOrderedField α] [FloorRing α]

theorem sub_half_lt_round (x : α) : x - 1 / 2 < round x := by
  rw [round_eq x, show x - 1 / 2 = x + 1 / 2 - 1 by nlinarith]
  exact Int.sub_one_lt_floor (x + 1 / 2)

theorem round_le_add_half (x : α) : round x ≤ x + 1 / 2 := by
  rw [round_eq x]
  exact Int.floor_le (x + 1 / 2)
