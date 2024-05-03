/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  intro a h1 h2

  have h3 : a-2 ≤ 1 := by addarith[h2]
  have h4 : -1 ≤ a-2 := by addarith[h1]

  have h5 : (a-2) ^2 ≤ 1^2 := by
    apply sq_le_sq'
    exact h4
    exact h3

  calc
    (a-2)^2 ≤ 1^2 := h5
    _ = 1 := by ring

  intro y
  intro h
  have h1 := h 1 (by numbers) (by numbers)
  have h2 := h 3 (by numbers) (by numbers)

  have h3 := calc
    (y-2) ^ 2 = ((1-y)^2 + (3-y)^2 - 2)/2 := by ring
    _ ≤ (1+1-2)/2 := by rel[h1, h2]
    _ = 0 := by ring

  have h4 : 0 ≤  (y-2)^2 := by extra

  have h5 : (y-2)^2 = 0 := le_antisymm h3 h4

  rw[sq] at h5

  rw[mul_eq_zero] at h5

  obtain hy | hy := h5
  repeat addarith[hy]


example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, hr3⟩ := hr
  obtain ⟨q, hr3⟩ := hr3
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  ring
  intro y
  intro h
  calc
    y = (4 * y -3) /4 + 3/4 := by ring
    _ = 9 /4 + 3/4 := by rw[h]
    _ = 3 := by ring

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  intro a
  apply Nat.zero_le
  intro y h
  have h1 := h 0
  apply Nat.le_zero.mp h1

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  dsimp
  constructor
  . constructor
    . numbers
    . constructor
      . numbers
      . use 3
        ring
  . intro y h
    obtain ⟨hy1, hy2, q, hy3⟩ := h
    have h1 := calc
      3 * q = 11-y := by rw[hy3]
      _ > 11-3 := by rel[hy2]
      _ > 3 * 2 := by numbers

    cancel 3 at h1

    have h2 := calc
      3 * q = 11-y := by rw[hy3]
      _ ≤ 11-0 := by rel[hy1]
      _ < 3 * 4 := by numbers

    cancel 3 at h2

    interval_cases q

    addarith[hy3]
