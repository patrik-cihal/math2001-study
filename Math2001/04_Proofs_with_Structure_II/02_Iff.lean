/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    dsimp [Int.ModEq] at h
    obtain ⟨k, hk⟩ := h
    dsimp[Odd]
    use k
    calc
      n = (n-1)+1 := by ring
      _ = 2*k + 1 := by rw[hk]

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    dsimp [Int.ModEq] at h
    have h2 : (n-0) = n := by ring
    rw[h2] at h
    exact h

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  . intro h
    have h2 := calc (x+3) * (x-2)
                    = (x^2)+x-6 := by ring
                  _ = 0 := h
    obtain hx | hx := eq_zero_or_eq_zero_of_mul_eq_zero h2
    left
    addarith[hx]
    right
    addarith[hx]
  . intro h
    obtain hx | hx := h
    . rw[hx]
      ring
    . rw[hx]
      ring

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  . intro h
    have h1 := calc (2*a-5) ^ 2
      _ = 4 * (a^2 - 5 * a + 5) + 5 := by ring
      _ ≤ 4 * (-1) + 5 := by rel[h]
      _ = 1 ^ 2 := by ring

    have h2 : -1 ≤ 2*a-5 ∧ 2*a -5 ≤ 1 := by
      apply abs_le_of_sq_le_sq' h1
      numbers

    have h3 := calc
      2*2 = -1 + 5 := by ring
      _ ≤ 2* a - 5 + 5 := by rel[h2.left]
      _ = 2 * a := by ring

    cancel 2 at h3

    have h4 := calc
      2 * a = 2* a -5 + 5 := by ring
      _ ≤ 1 + 5 := by rel[h2.right]
      _ = 2 * 3 := by ring

    cancel 2 at h4

    interval_cases a

    left
    rfl
    right
    rfl
  . intro h
    obtain ha | ha := h
    rw[ha]
    numbers
    rw[ha]
    numbers

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain hn2 | hn2 := hn2
  use 2
  calc
    n = (n-4) + 4 := by ring
    _ = 0 + 4 := by rw[hn2]
    _ = 2 * 2 := by ring
  use 3
  calc
    n = (n-6) + 6 := by ring
    _ = 0 + 6 := by rw[hn2]
    _ = 2 * 3 := by ring

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn

  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  obtain hn2 | hn2 := hn1
  use 2
  calc
    n = 4 := by addarith[hn2]
    _ = 2 * 2 := by ring
  use 3
  calc
    n = 6 := by addarith[hn2]
    _ = 2 * 3 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  intro h
  calc
    x = (2 * x - 1) /2 + 1/2 := by ring
    _ = 11 / 2 + 1/2 := by rw[h]
    _ = 6 := by ring

  intro h
  rw[h]
  ring

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  intro h
  dsimp[Dvd.dvd] at *
  obtain ⟨c, hc⟩ := h
  constructor
  . use 9 * c
    calc
      n = 63 * c := hc
      _ = 7 * (9 * c) := by ring
  . use 7 * c
    calc
      n = 63 * c := hc
      _ = 9 * (7*c) := by ring
  intro h
  obtain ⟨a, ha⟩ := h.left
  obtain ⟨b, hb⟩ := h.right
  use 4*a-5*b
  calc
    n = 36 * n- 35 * n := by ring
    _ = 36 * (7 * a) - 35 * n := by rw[ha]
    _ = 36 * (7 * a) - 35 * (9*b) := by rw[hb]
    _ = 63 * (4 * a - 5 * b) := by ring

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  dsimp[Int.ModEq]
  have h : a-0 = a := by ring
  rw[h]

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k, hk⟩ := hab
  rw[hk]
  use 2 * a^2 * k^3 - a * k^2 + 3*k
  ring

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  . intro h
    have h1 :=
      calc k^2
        _ ≤ 6 := h
        _ < 3^2 := by numbers
    cancel 2 at h1
    interval_cases k
    left
    rfl
    right
    left
    rfl
    right
    right
    rfl
  . intro h
    obtain hk | hk | hk := h
    repeat
      rw[hk]
      numbers
