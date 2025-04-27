import Mathlib.Data.Nat.Fib.Basic

inductive Bin where | a : Bin | b : Bin
open Bin

def FibWord (n: Nat): List Bin :=
  match n with
  | 0 => []
  | 1 => [b]
  | 2 => [a]
  | n + 3 => FibWord (n + 2) ++ FibWord (n + 1)

example : FibWord 1 = [b] := by rw [FibWord]
example : FibWord 2 = [a] := by rw [FibWord]
example : FibWord 3 = [a, b] := by repeat (rw [FibWord]; repeat trivial)
example : FibWord 4 = [a, b, a] := by repeat (rw [FibWord]; repeat trivial)
example : FibWord 5 = [a, b, a, a, b] := by repeat (rw [FibWord]; repeat trivial)

theorem fib_word_length (n: Nat) : (FibWord n).length = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | h n ih => match n with
  | 0 | 1 | 2 => trivial
  | n + 3 => simp +arith [FibWord, ih (n + 2), ih (n + 1), ← Nat.fib_add_two]
