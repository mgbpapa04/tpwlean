import Mathlib.Tactic

theorem apple (x y : ℤ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

#print apple
