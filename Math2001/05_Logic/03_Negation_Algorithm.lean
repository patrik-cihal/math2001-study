/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel

math2001_init
set_option pp.funBinderTypes true


example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · intro h
    intro h2
    obtain hnp | hnq := h
    have hp := h2.left
    contradiction
    have hq := h2.right
    contradiction

example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by rel [not_exists]

def k := @not_and

example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 :=
  calc ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
        ↔ ∃ n : ℤ, ¬ (∃ m : ℤ, n^2 < m ∧ m < (n+1)^2) := by rel[not_forall]
      _ ↔ ∃ n : ℤ, ∀ m : ℤ, ¬(n^2 < m ∧ m < (n+1)^2) := by rel[not_exists]
      _ ↔ ∃ n : ℤ, ∀ m : ℤ, (¬(n^2 < m) ∨ ¬(m < (n+1)^2)) := by rel[not_and_or]
      _ ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 := by rel[not_lt]

#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n : ℤ, ∀ m : ℤ, m ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ m


#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      2 < 2^2 := by numbers
      _ ≤ n^2 := by rel[hn]

/-! # Exercises -/


example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor
  intro h
  by_cases P
  assumption
  contradiction
  intro h
  by_cases ¬P
  contradiction
  assumption

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  intro h
  by_cases hq : Q
  have hc := h (fun _ => hq)
  contradiction
  by_cases hp : P
  exact And.intro hp hq
  have hc := h (fun p => by contradiction)
  contradiction
  intro h
  intro h2
  by_cases hp : P
  have hq := h2 hp
  have hqc := h.right
  contradiction
  have hpc := h.left
  contradiction



example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  . intro h
    by_contra h2
    have hc := h (by
      intro x
      by_contra hpx
      have he : ∃ x, ¬ P x := ⟨x, hpx⟩
      contradiction
    )
    contradiction
  . intro h
    obtain ⟨a, hnp⟩ := h
    intro h2
    have hc := h2 a
    contradiction



example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := calc
    (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
      ↔ (∃ a : ℤ, (¬ ∀ b : ℤ, (a*b = 1 → a = 1 ∨ b = 1))) := by rel[not_forall]
    _ ↔ (∃ a b : ℤ, (¬ (a*b = 1 → a = 1 ∨ b = 1))) := by rel[not_forall]
    _ ↔ (∃ a b : ℤ, ((a*b = 1 ∧ ¬(a = 1 ∨ b = 1)))) := by rel[not_imp]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by rel[not_or]

example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) :=
  calc (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x)
      ↔ ∀ x :ℝ, ¬ ∀ y: ℝ, y ≤ x := by rel[not_exists]
    _ ↔ ∀ x : ℝ, ∃ y : ℝ, ¬ y≤ x := by rel[not_forall]
    _ ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) := by rel[not_le]

example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 :=
  calc ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5)
      ↔ ∀ m : ℤ, ¬ ∀ n : ℤ, m = n+5 := by rel[not_exists]
    _ ↔ ∀ m : ℤ, ∃ n : ℤ, ¬ m = n+5 := by rel[not_forall]

#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 0.5
  numbers

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  by_cases h : 4.5 < t
  left
  calc
    4 < 4.5 := by numbers
    _ < t := h
  right

  rw[not_lt] at h
  calc
    t ≤ 4.5 := h
    _ < 5 := by numbers

example : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg
  intro k
  intro h
  by_cases hk : k≤3
  . have hc := calc
      7 = 2*k := h
      _ ≤ 2 * 3 := by rel[hk]
      _ = 6 := by ring

    numbers at hc
  . push_neg at hk
    have hk : 4 ≤ k := hk
    have hc := calc
      7 = 2 * k := h
      _ ≥ 2 * 4 := by rel[hk]
      _ = 8 := rfl
    numbers at hc

example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  right
  use k
  constructor
  exact hk
  constructor <;> assumption

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro a
  use 2*a^2
  calc
    2*a^3 < 2*a^3 + 7 := by extra
    _ = 2*a^2*a + 7 := by ring

def awiofj := @Nat.le_of_lt_add_of_dvd

example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    dsimp[Prime] at hp
    push_neg at hp
    obtain hp | hp := hp
    have hpc : ¬ 2 ≤ p := not_le.mpr hp
    contradiction
    obtain ⟨m, hm⟩ := hp
    have hmc := H m
    by_cases hm2 : 2≤ m
    . have hmp := hm.left
      have hmp2 := hm.right.right
      have hp3 : p≠ 0 := by exact Nat.not_eq_zero_of_lt hp2
      have hm3 : m < p := by
        by_contra hmp3
        push_neg at hmp3
        have hmp3 : p = m ∨ p< m := by exact Nat.eq_or_lt_of_le hmp3
        obtain hmp3 | hmp3 := hmp3
        exact hmp2 hmp3.symm
        obtain ⟨k, hk⟩ := hmp
        by_cases hp4:p > 0
        have hp4 : p≥1 := hp4
        have hk2 : k ≠ 0 := by
          have h := calc m*k = p := hk.symm
            _ ≠ 0 := hp3
          exact (ne_zero_and_ne_zero_of_mul h).right
        have hk2 : k≥1 := by exact Nat.pos_of_ne_zero hk2
        have hc := calc
          m * k ≥ m * 1 := by rel[hk2]
          _ = m := by ring
          _ > p := hmp3
        have : p ≠ m*k := by exact Nat.ne_of_lt hc
        contradiction
        have hp3 : p = 0 := by exact Nat.eq_zero_of_not_pos hp4
        contradiction
      have hmdc := hmc hm2 hm3
      contradiction
    . have hm2 : m < 2 := not_le.mp hm2
      interval_cases m
      have hc := hm.left
      obtain ⟨k, hk⟩ := hc
      rw[zero_mul] at hk
      exact hm.right.right hk.symm
      have hc := hm.right.left
      exact hc rfl
  push_neg at H
  exact H
