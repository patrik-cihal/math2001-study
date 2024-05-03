/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h :=
    calc 13 = 3*k := hk
      _ ≥ 3 * 5 := by rel[h5]
      _ ≥ 15 := by numbers
    numbers at h

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n, h⟩ := h
  obtain hn | hn := le_or_gt n 1
  have h2 := calc
    2 = n^2 := h.symm
    _ ≤ 1^2 := by rel[hn]
    _ = 1 := by ring
  have hc2 : ¬(2≤1) := by numbers
  contradiction
  have hn : n ≥ 2 := hn
  have h2 := calc
    2 = n^2 := h.symm
    _ ≥ 2^2 := by rel[hn]
    _ = 4 := by ring
  have hc2 : ¬(2≥4) := by numbers
  contradiction

example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction


example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  . intro h1 h2
    rw [Int.even_iff_modEq] at h2
    rw [Int.odd_iff_modEq] at h1
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h2]
      _ ≡ 1 [ZMOD 2] := by rel [h1]
    numbers at h
  . intro h
    obtain hn | hn := Int.even_or_odd n
    . contradiction
    . exact hn

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc (1:ℤ) ≡ 3*1 + 1 [ZMOD 3] := by extra
      _ = 2^2 := by ring
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!

example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1
  have h2 := calc b * q < a := hq₁
    _ = b*k := hk
  cancel b at h2
  have h2 : ¬(q+1 > k) := by exact Int.not_lt.mpr h2
  contradiction

example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · use m
    rw[mul_comm]
    exact hl
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 : l < T
  · have := calc T*l ≤ m*l := by rel[hmT]
      _ = p := hl.symm
      _ < T^2 := hTp
      _ = T*T := by ring
    cancel T at this

  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro h
  obtain ⟨t, ht1, ht2⟩ := h
  have ht3 := calc t ≤ 4 := ht1
      _ < 5 := by numbers
  have : ¬(t≥5) := not_le.mpr ht3
  contradiction

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro h
  have ⟨a, ha1, ha2⟩ := h
  have ha1 :=
    calc a^6 = a^2*a^2*a^2 := by ring
      _ ≤ 8 * 8 * 8 := by rel[ha1]
      _ < 900 := by numbers
  have ha2 :=
    calc a^6 = a^3 * a^3 := by ring
      _ ≥ 30 * 30 := by rel[ha2]
      _ = 900 := by numbers

  have hca2 := not_lt.mpr ha2

  contradiction

example : ¬ Int.Even 7 := by
  intro h
  dsimp[Int.Even] at h
  have : 2 ∣ 7 := by exact ofNat_dvd.mp h
  have hc : ¬2 ∣ 7
  . apply Nat.not_dvd_of_exists_lt_and_lt
    use 3
    constructor <;> numbers
  contradiction

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  intro h
  obtain ⟨h1, h2⟩ := h
  have hn : n = 4 := by addarith[hn]
  have hc := calc
    16 = 4*4 := by ring
    _ = n*n := by rw[hn]
    _ = n^2 := by ring
    _ = 10 := h2
  numbers at hc

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  intro h

  obtain h | h := h
  have hx2 : x > -3 := by
    have :=
      calc (-x)^2 = x^2 := by ring
        _ < 9 := hx
        _ = 3^2 := by ring
    cancel 2 at this
    exact neg_lt.mpr this

  have := not_le.mpr hx2
  contradiction

  have hx2 : x < 3 := by
    have :=
      calc x^2 < 9 := hx
        _ = 3^2 := by numbers
    cancel 2 at this

  have := not_le.mpr hx2
  contradiction

example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  intro h
  obtain ⟨n, h⟩ := h
  have hn1 := h (n+1) (by extra)
  have hn2 := h (n+2) (by extra)
  obtain ⟨k, hk⟩ := hn1
  have : ¬2 ∣ (n+2) := by
    apply Nat.not_dvd_of_exists_lt_and_lt
    use k
    constructor
    . calc 2*k = n+1 := hk.symm
        _  < n+1+1 := by extra
        _ = n+2 := by ring
    . calc n+2 < n+2+1 := by extra
        _ = n+1+2 := by ring
        _ = 2*k+2 := by rw[hk]
        _ = 2*(k+1) := by ring

  contradiction

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro h
  mod_cases n%4
  have hc := calc
    0 = 0^2 := by ring
    _ ≡ n^2 [ZMOD 4] := by rel[H]
    _ ≡ 2 [ZMOD 4] := h
  have hcc : ¬(0≡2 [ZMOD 4]) := by numbers at hc
  contradiction
  have hc := calc
    1 = 1^2 := by ring
    _ ≡ n^2 [ZMOD 4] := by rel[H]
    _ ≡ 2 [ZMOD 4] := h
  have hcc : ¬(1≡2 [ZMOD 4]) := by numbers at hc
  contradiction
  have hc := calc
    0 ≡ 1*4 [ZMOD 4] := by extra
    _ = 2 ^ 2 := by ring
    _ ≡ n^2 [ZMOD 4] := by rel[H]
    _ ≡ 2 [ZMOD 4] := h
  have hcc : ¬(0≡2 [ZMOD 4]) := by numbers at hc
  contradiction
  have hc := calc
    1 ≡ 2*4+1 [ZMOD 4] := by extra
    _ = 3^2 := by ring
    _ ≡ n^2 [ZMOD 4] := by rel[H]
    _ ≡ 2 [ZMOD 4] := h
  have hcc : ¬(1≡2 [ZMOD 4]) := by numbers at hc
  contradiction

example : ¬ Prime 1 := by
  dsimp[Prime]
  intro h
  have hc := h.left
  numbers at hc

example : Prime 97 := by
  apply better_prime_test (T := 10)
  numbers
  numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 48
    constructor <;> numbers
  · use 32
    constructor <;> numbers
  · use 24
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 16
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 12
    constructor <;> numbers
  · use 10
    constructor <;> numbers
