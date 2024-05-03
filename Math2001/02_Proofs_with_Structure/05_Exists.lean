/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt' : 0 < x*(-t) := calc
      0 < -x*t := by addarith[hxt]
      _ = x*(-t) := by ring
    have hx' : 0≤ x := by addarith[hx]
    cancel x at hxt'
    have hxt' : t < 0 := by addarith[hxt']
    exact ne_of_lt hxt'

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  rfl


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  ring

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use (a+1), a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p+q)/2
  constructor
  . calc
      p = (p+p) / 2 := by ring
      _ < (p+q) / 2 := by rel[h]
  . calc
      (p+q)/2 < (q+q)/2 := by rel[h]
      _ = q := by ring

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  ring

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6, 7
  ring

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  numbers
  numbers


example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3
  ring

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  sorry

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, hta⟩ := h
  by_contra ht
  rw[ht] at hta
  rw[mul_one] at hta
  exact LT.lt.false hta

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ham⟩ := h
  obtain ha | ha := le_or_succ_le a 2
  apply ne_of_lt
  calc
    m
      = 2 * a := ham.symm
    _ ≤ 2 * 2 := by rel[ha]
    _ < 5 := by numbers

  apply ne_of_gt
  calc
    5
      < 2 * 3 := by numbers
    _ ≤ 2 * a := by rel[ha]
    _ = m := ham

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  use n^2+3

  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
