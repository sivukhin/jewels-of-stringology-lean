import Mathlib.Data.Nat.Fib.Basic

def FibWord (n: Nat): List Nat :=
  match n with
  | 0 => []
  | 1 => [1]
  | 2 => [0]
  | n + 3 => FibWord (n + 2) ++ FibWord (n + 1)

example : FibWord 1 = [1] := by rw [FibWord]
example : FibWord 2 = [0] := by rw [FibWord]
example : FibWord 3 = [0, 1] := by repeat (rw [FibWord]; repeat trivial)
example : FibWord 4 = [0, 1, 0] := by repeat (rw [FibWord]; repeat trivial)
example : FibWord 5 = [0, 1, 0, 0, 1] := by repeat (rw [FibWord]; repeat trivial)

theorem fib_word_length (n: Nat) : (FibWord n).length = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | h n ih => match n with
  | 0 | 1 | 2 => trivial
  | n + 3 => simp +arith [FibWord, ih (n + 2), ih (n + 1), ← Nat.fib_add_two]
