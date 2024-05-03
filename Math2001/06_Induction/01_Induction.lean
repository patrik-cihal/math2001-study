/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Nat


example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra


example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    left
    dsimp[Even]
    use 0
    numbers
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · right
      use x
      rw[hx]
    · left
      use x+1
      rw[hx]
      ring

example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  . use 0
    ring
  . obtain ⟨x, hx⟩ := IH
    obtain ⟨y, hy⟩ := h
    use a*x + b^k*y
    calc a^(k+1)-b^(k+1) = a*(a^k-b^k) + b^k*(a-b) := by ring
      _ = a*(d*x) + b^k * (d*y) := by rw[hx, hy]
      _ = d*(a*x + b^k*y) := by ring

example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 15] := by rel [hk]
        _ = 4 := by numbers
    · left
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 15] := by rel [hk]
        _ = 15 * 1 + 1 := by numbers
        _ ≡ 1 [ZMOD 15] := by extra


example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc 2^(k+1) = 2 * 2^k := by ring
      _ ≥ 2*k^2 := by rel[IH]
      _ = k^2 + k*k := by ring
      _ ≥ k^2 + 4 *k := by rel[hk]
      _ = k^2 + 2*k + 2*k := by ring
      _ ≥ k^2 + 2*k+2*4 := by rel[hk]
      _ = (k+1)^2 + 7 := by ring
      _ ≥ (k+1)^2 := by extra


/-! # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with k ih
  .
    numbers
  .
    calc
      3^(k+1) = (3^k) * 3 := by ring
      _ ≥ (k^2 + k+1) * 3 := by rel[ih]
      _ = k^2 + 2*k + 1 + 2 + k + 2*k^2 := by ring
      _ = (k+1)^2 + (k+1) + 1 + 2*k^2 := by ring
      _ ≥ (k+1)^2 + (k+1) +1 := by extra

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k ih
  .
    have := calc
      (1+a)^0 = 1 := by rfl
      _ = 1 + 0 * a := by ring
    exact Eq.ge this
  .
    have ha : 0≤1+a := by addarith[ha]
    calc
      (1+a)^(k+1) = (1+a)^k * (1+a) := by ring
      _ ≥ (1 + k*a) * (1+a) := by rel[ih]
      _ = 1+a+k*a+k*a^2 := by ring
      _ = a^2*k + 1 + (k+1)*a := by ring
      _ ≥ 1 + (k+1) * a := by extra


example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  simple_induction n with k ih
  .
    left
    use 0
    numbers
  .
    obtain ih | ih := ih
    right
    calc 5^(k+1)
      _ = ((5^k * 5) : ℤ) := by ring
      _ ≡ 1 * 5 [ZMOD 8] := by rel[ih]
      _ = 5 := by rfl

    left
    calc 5^(k+1)
      _ = ((5^k * 5) : ℤ) := by ring
      _ ≡ 5 * 5 [ZMOD 8] := by rel[ih]
      _ = 8 * 3 + 1 := by ring
      _ ≡ 1 [ZMOD 8] := by extra


example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  simple_induction n with k ih
  .
    left
    use 0
    numbers
  .
    obtain ih | ih := ih
    right
    calc 6^(k+1)
      _ = ((6^k * 6) : ℤ) := by ring
      _ ≡ 1 * 6 [ZMOD 7] := by rel[ih]
      _ = 6 := by rfl

    left
    calc 6^(k+1)
      _ = ((6^k * 6) : ℤ) := by ring
      _ ≡ 6 * 6 [ZMOD 7] := by rel[ih]
      _ = 7 * 5 + 1 := by ring
      _ ≡ 1 [ZMOD 7] := by extra

example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  simple_induction n with k ih
  .
    left
    use 0
    numbers
  .
    obtain ih | ih | ih := ih
    right
    right
    calc
      4^(k+1)
          = ((4^k*4) : ℤ) := by ring
        _ ≡ 1*4 [ZMOD 7] := by rel[ih]
        _ = 4 := rfl
    left

    calc
      4^(k+1)
          = ((4^k*4) : ℤ) := by ring
        _ ≡ 2*4 [ZMOD 7] := by rel[ih]
        _ = 7*1 + 1 := by ring
        _ ≡ 1 [ZMOD 7] := by extra

    right
    left
    calc
      4^(k+1)
          = ((4^k*4) : ℤ) := by ring
        _ ≡ 4*4 [ZMOD 7] := by rel[ih]
        _ = 7*2 + 2 := by ring
        _ ≡ 2 [ZMOD 7] := by extra

example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 10
  intro x
  intro hx
  induction_from_starting_point x, hx with k hk ih

  .
    numbers
  .
    calc
      3^(k+1) = 3^k * 3 := by rfl
      _ ≥ (2^k + 100) * (3 : ℤ) := by rel[ih]
      _ = 2^k*3 + 300 := by ring
      _ = 2^(k+1) + 100 + (2^k + 200) := by ring
      _ ≥ 2^(k+1)+100 := by extra

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  use 5
  intro n
  intro hn
  induction_from_starting_point n, hn with k hk ih
  .
    numbers
  .
    calc
      2^(k+1) = 2^k*2 := by ring
      _ ≥ (k^2 + 4)*2 := by rel[ih]
      _ = k^2 + k*k + 8 := by ring
      _ ≥ k^2 + 5*k + 8 := by rel[hk]
      _ = k^2+2*k+1+3*k+7 := by ring
      _ = (k+1)^2 + 4 + (3*k + 3) := by ring
      _ ≥ (k+1)^2 + 4 := by extra

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  use 10
  intro n
  intro hn
  induction_from_starting_point n, hn with k hk ih
  .
    numbers
  .
    calc 2^(k+1)
      _ = 2^k * 2 := by ring
      _ ≥ k^3 * 2 := by rel[ih]
      _ = k^3 + k*k^2 := by ring
      _ ≥ k^3 + 10*k^2 := by rel[hk]
      _ = k^3 + 5*k^2 + 5*k*k := by ring
      _ ≥ k^3 + 5*k^2 + 5 * 10 * k := by rel[hk]
      _ = k^3 + 5*k^2 + 40 * k + 10 * k := by ring
      _ ≥ k^3 + 5*k^2 + 40 * k + 10 * 10 := by rel[hk]
      _ = k^3 + 3*k^2 + 3*k + 1 + (2*k^2+37*k+99) := by ring
      _ ≥ k^3 + 3*k^2 + 3*k + 1 := by extra
      _ = (k+1)^3 := by ring

theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  simple_induction n with k ih
  .
    use 0
    ring
  .
    obtain ⟨l, hl⟩ := ih
    obtain ⟨m, hm⟩ := ha
    use 2*l*m+m+l

    calc a^(k+1)
      _ = a^k*a := by ring
      _ = (2*l+1)*(2*m+1) := by rw[hl, hm]
      _ = 2*(2*l*m+m+l)+1 := by ring


def k := Int.odd_iff_not_even

theorem Nat.even_of_pow_even {a n : ℕ} (ha : Even (a ^ n)) : Even a := by
  by_contra hc
  have hc : Odd a := a.odd_iff_not_even.mpr hc
  have hc := Odd.pow hc n
  have hc := (Nat.odd_iff_not_even (a^n)).mp hc
  contradiction
