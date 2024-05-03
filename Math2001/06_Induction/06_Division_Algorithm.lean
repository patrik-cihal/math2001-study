/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init


def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by _ n d => 2 * n - d

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by _ n d => 2 * n - d


#eval fmod 11 4 -- infoview displays `3`
#eval fdiv 11 4 -- infoview displays `2`


theorem fmod_add_fdiv (n d : ℤ) : fmod n d + d * fdiv n d = n := by
  rw [fdiv, fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_add_fdiv (n + d) d -- inductive hypothesis
    calc fmod (n + d) d + d * (fdiv (n + d) d - 1)
        = (fmod (n + d) d + d * fdiv (n + d) d) - d := by ring
      _ = (n + d) - d := by rw [IH]
      _ = n := by ring
  · -- case `0 < d * (n - d)`
    have IH := fmod_add_fdiv (n - d) d -- inductive hypothesis
    calc fmod (n - d) d + d * (fdiv (n - d) d + 1)
        = (fmod (n - d) d + d * fdiv (n - d) d) + d := by ring
        _ = n := by addarith [IH]
  · -- case `n = d`
    calc 0 + d * 1 = d := by ring
      _ = n := by rw [h3]
  · -- last case
    ring
termination_by _ n d => 2 * n - d



theorem fmod_nonneg_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : 0 ≤ fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_nonneg_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_nonneg_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    extra
  · -- last case
    cancel d at h1
termination_by _ n d hd => 2 * n - d


theorem fmod_lt_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : fmod n d < d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_lt_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_lt_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have h4 :=
    calc 0 ≤ - d * (n - d) := by addarith [h2]
      _ = d * (d - n) := by ring
    cancel d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply h3
termination_by _ n d hd => 2 * n - d


example (a b : ℤ) (h : 0 < b) : ∃ r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  constructor
  · apply fmod_nonneg_of_pos a h
  constructor
  · apply fmod_lt_of_pos a h
  · use fdiv a b
    have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    addarith [Hab]

/-! # Exercises -/


theorem lt_fmod_of_neg (n : ℤ) {d : ℤ} (hd : d < 0) : d < fmod n d := by
  rw[fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  .
    have ih := lt_fmod_of_neg (n+d) hd
    apply ih
  .
    have ih := lt_fmod_of_neg (n-d) hd
    apply ih
  .
    apply hd
  .
    have h2 : (n-d) ≥ 0 := by exact nonneg_of_mul_nonpos_right h2 hd
    have h2 : n ≥ d := by addarith[h2]
    have h2 : n > d := by exact Ne.lt_of_le (Ne.symm h3) h2
    exact h2

termination_by _ n d hd => 2*n -d

def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if 0 < - n then
    T (-n)
  else
    0
termination_by T n => 3 * n - 1

theorem T_eq (n : ℤ) : T n = n ^ 2 := by
  rw[T]
  split_ifs with h1 h2 <;> push_neg at *
  .
    have ih := T_eq (1-n)
    rw[ih]
    ring
  .
    have ih := T_eq (-n)
    rw[ih]
    ring
  .
    have hn : n ≥ 0 := by exact Int.nonneg_of_neg_nonpos h2
    have hn : n = 0 := by exact Int.le_antisymm h1 hn
    rw[hn]
    ring
termination_by _ n => 3 *n -1

theorem uniqueness (a b : ℤ) (h : 0 < b) {r s : ℤ}
    (hr : 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b])
    (hs : 0 ≤ s ∧ s < b ∧ a ≡ s [ZMOD b]) : r = s := by
  obtain ⟨hr1, hr2, k, hk⟩ := hr
  obtain ⟨hs1, hs2, l, hl⟩ := hs

  have hr3 : -r = b*k-a := by addarith[hk]
  have hs3 : -s = b*l-a := by addarith[hl]

  have hkl : k = l := by
    apply le_antisymm
    apply Int.not_lt.mp
    intro hkl
    have hkl : k ≥ l+1 := hkl
    have hbka : b*k ≥ b*(l+1) := by exact (mul_le_mul_left h).mpr hkl
    have hsb : -s > -b := by exact Int.neg_lt_neg hs2
    have hr := by
      calc -r = b*k-a := hr3
        _ ≥ b*(l+1)-a := by rel[hbka]
        _ = b*l-a + b := by ring
        _ = (-s) + b := by rw[hs3]
        _ > (-b) + b := by exact Int.add_lt_add_right hsb b
        _ = 0 := by ring

    have hr : r < 0 := by exact Int.neg_of_neg_pos hr

    have : ¬ 0 ≤ r := by exact Int.not_le.mpr hr
    contradiction

    apply Int.not_lt.mp
    intro hkl
    have hkl : l ≥ k+1 := hkl
    have hbka : b*l ≥ b*(k+1) := by exact (mul_le_mul_left h).mpr hkl
    have hsb : -r > -b := by exact Int.neg_lt_neg hr2
    have hr := by
      calc -s = b*l-a := hs3
        _ ≥ b*(k+1)-a := by rel[hbka]
        _ = b*k-a + b := by ring
        _ = (-r) + b := by rw[hr3]
        _ > (-b) + b := by exact Int.add_lt_add_right hsb b
        _ = 0 := by ring

    have hs : s < 0 := by exact Int.neg_of_neg_pos hr

    have : ¬ 0 ≤ s := by exact Int.not_le.mpr hs
    contradiction



  rw[hkl] at hr3
  rw[←hs3] at hr3


  exact Int.neg_inj.mp hr3




example (a b : ℤ) (h : 0 < b) : ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b

  have ha : 0≤fmod a b ∧ fmod a b < b ∧ a ≡ fmod a b [ZMOD b] := by
    constructor
    · apply fmod_nonneg_of_pos a h
    constructor
    · apply fmod_lt_of_pos a h
    · use fdiv a b
      have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
      addarith [Hab]

  constructor
  .
    apply ha
  .
    intro y
    intro hy

    apply uniqueness a b h
    apply hy
    apply ha
