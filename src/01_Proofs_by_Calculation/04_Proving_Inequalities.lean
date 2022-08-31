/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import tactics.inequalities


example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : 
  y ≥ 4 :=
calc y = (y + 2 * x) - 2 * x : by ring
... ≥ 3 - 2 * x : by ineq_tac [hy]
... = 9 - 2 * (x + 3) : by ring
... ≥ 9 - 2 * 2 : by ineq_tac [hx]
... ≥ 4 : by norm_num


example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : 
  r ≤ 3 :=
calc r = ((s + r) + r - s) / 2 : by sorry
... ≤ (3 + (s + 3) - s) / 2 : by sorry
... = 3 : by sorry


example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : 
  x + y < 2 :=
sorry

example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) : 
  3 * a * b + a ≤ 7 * b + 72 :=
calc 3 * a * b + a
  = 3 * a * b + 0 + 0 + a : by sorry
... ≤ 3 * a * b + 2 * b ^ 2 + a ^ 2 + a : by sorry
... = 2 * ((a + b) * b) + ((a + b) * a) + a : by sorry
... ≤ 2 * (8 * b) + (8 * a) + a : by sorry
... = 7 * b + 9 * (a + b) : by sorry
... ≤ 7 * b + 9 * 8 : by sorry
... = 7 * b + 72 : by sorry



example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B) (h5 : y ≤ B)
(h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
  u * y + v * x + u * v < 3 * A * B :=
sorry

example {t : ℚ} (ht : t ≥ 10) : 
  t ^ 2 - 3 * t - 17 ≥ 5 :=
calc t ^ 2 - 3 * t - 17
  = t * t - 3 *  - 17 : by sorry
... ≥ 10 * t - 3 * t - 17 : by sorry
... = 7 * t - 17 : by sorry
... ≥ 7 * 10 - 17 : by sorry
... ≥ 5 : by sorry



example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 :=
calc n = 0 + n : by ring
... ≤ m ^ 2 + n : by ineq_tac []
... ≤ 2 : by ineq_tac [h]


example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 :=
calc (x + y) ^ 2 = (x + y) ^ 2 + 0 : by sorry
... ≤ (x + y) ^ 2 + (x - y) ^ 2 : by sorry
... = 2 * (x ^ 2 + y ^ 2) : by sorry
... ≤ 2 * 1 : by sorry
... < 3 : by sorry

example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b :=
sorry

example {a b c : ℝ} :
  a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 :=
calc a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3)
    = 0 + 0 + 0 + a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) : by ring
... ≤ 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 
      + (b ^ 4 - c ^ 4) ^ 2
      + 4 * (a ^ 2 * b * c - b ^ 2 * c ^ 2) ^ 2 
      + a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) : by ineq_tac []
... = (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 : by ring


example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : 
  x ≥ -1 :=
sorry


example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : 
  a + b ≥ 3 :=
sorry

example {x : ℤ} (hx : x ≥ 9) : 
  x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
sorry

example {n : ℤ} (hn : n ≥ 10) : 
  n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 :=
sorry

example {n : ℤ} (h1 : n ≥ 5) :
  n ^ 2 - 2 * n + 3 > 14 :=
sorry

example {x : ℚ} :
  x ^ 2 - 2 * x ≥ -1 :=
sorry