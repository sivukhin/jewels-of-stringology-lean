import Mathlib.Tactic.SimpRw
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NthRewrite

variable { α : Type }

inductive Bin where | a : Bin | b : Bin
open Bin

def inverseBin (x: Bin): Bin := match x with
  | a => b
  | b => a

theorem inverse_is_involution (x: Bin) : inverseBin (inverseBin x) = x := by
  match x with
  | a | b => trivial

def inverseWord (w: List Bin): List Bin := w.map inverseBin

theorem inverseWord_is_involution (w: List Bin): inverseWord (inverseWord w) = w := by
  induction w with
  | nil => trivial
  | cons h t ih =>
    rw [inverseWord, inverseWord]
    rw [List.map_cons, List.map_cons]
    rw [← inverseWord, ← inverseWord]
    simp [inverse_is_involution, ih]

def TueMorseMorphism (x: Bin): List Bin := match x with
  | a => [a, b]
  | b => [b, a]

def Morphism (m: α → List α) (w: List α) := w.flatMap m

theorem morphism_distributive (m: α → List α) (w₁ w₂: List α) :
  (Morphism m w₁) ++ (Morphism m w₂) = Morphism m (w₁ ++ w₂) := by simp [Morphism]

theorem tue_morphism_inv_comm (w: List Bin) :
  inverseWord (Morphism TueMorseMorphism w) = (Morphism TueMorseMorphism (inverseWord w)) := by
  simp [inverseWord, inverseBin, Morphism, TueMorseMorphism]
  simp [List.map_flatMap]
  simp [List.flatMap_map]
  have eq : ∀ (x: Bin), List.map inverseBin (TueMorseMorphism x) = TueMorseMorphism (inverseBin x) := by
    intro x
    match x with
    | a | b => trivial
  simp_rw [eq]

theorem morphism_const_length (m: α → List α) (l: Nat) (hl: ∀ (x: α), (m x).length = l) (w: List α) :
  (Morphism m w).length = w.length * l := by
  simp [Morphism]
  conv in (m _).length => apply hl
  induction w with
  | nil => simp
  | cons h t ih => simp +arith [ih, Nat.add_mul]

example : Morphism TueMorseMorphism (Morphism TueMorseMorphism [a]) = [a, b, b, a] := by trivial

def TueMorseWord (n: Nat): List Bin := match n with
  | 0 => [a]
  | n + 1 => Morphism TueMorseMorphism (TueMorseWord (n))

def TueMorseWordAlt (n: Nat): List Bin := match n with
  | 0 => [a]
  | n + 1 => (TueMorseWordAlt n) ++ inverseWord (TueMorseWordAlt n)

example : TueMorseWord 3 = [a, b, b, a, b, a, a, b] := by
  simp [TueMorseWord, Morphism, TueMorseMorphism, List.flatMap_eq_foldl]

example : TueMorseWordAlt 3 = [a, b, b, a, b, a, a, b] := by
  simp [TueMorseWordAlt, inverseWord, inverseBin]

theorem tue_morse_morphism_length (x: Bin) : (TueMorseMorphism x).length = 2 := by
  match x with
  | a | b => trivial

theorem tue_morse_word_length (n: Nat): (TueMorseWord n).length = 2^n := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [TueMorseWord]
    rw [morphism_const_length TueMorseMorphism 2 tue_morse_morphism_length (TueMorseWord n)]
    omega

theorem tue_morse_word_alt_length (n: Nat): (TueMorseWordAlt n).length = 2^n := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [TueMorseWordAlt]
    simp [ih, inverseWord]
    omega

theorem tue_morse_def_eq (n: Nat) : TueMorseWord n = TueMorseWordAlt n := by
  induction n using Nat.strong_induction_on with
  | h n ih => match n with
    | 0 | 1 => trivial
    | n + 2 =>
      let x := TueMorseWord (n + 1)
      let x_l := x.take (2^n)
      let x_r := x.drop (2^n)

      let y := TueMorseWordAlt (n + 1)
      let y_l := y.take (2^n)
      let y_r := y.drop (2^n)

      have x_l_eq_y_l : x_l = y_l := by simp [x_l, y_l, x, y, ih]
      have x_r_eq_y_r : x_r = y_r := by simp [x_r, y_r, x, y, ih]

      have y_l_eq_tn : y_l = TueMorseWordAlt n := by
        simp only [y, y_l, TueMorseWordAlt]
        rw [List.take_append_of_le_length, List.take_of_length_le]
        repeat rw [tue_morse_word_alt_length]

      have : y_r = inverseWord (TueMorseWordAlt n) := by
        simp only [y, y_r, TueMorseWordAlt]
        rw [List.drop_append_of_le_length, List.drop_of_length_le]
        simp
        repeat rw [tue_morse_word_alt_length]

      have : y_l ++ inverseWord y_l = y := by simp_all only [y, y_l, TueMorseWordAlt]
      have : y_l ++ y_r = y := by simp_all only
      have y_r_eq_not_y_l : y_r = inverseWord y_l := by simp_all [inverseWord_is_involution]

      have y_l_morph : (Morphism TueMorseMorphism y_l) = TueMorseWordAlt (n + 1) := by
        rw [← x_l_eq_y_l]
        rw [← ih]
        rw [TueMorseWord]
        rw [x_l_eq_y_l, y_l_eq_tn]
        rw [ih]
        repeat simp

      have x_break : (Morphism TueMorseMorphism x_l) ++ (Morphism TueMorseMorphism x_r) =
              Morphism TueMorseMorphism x := by
        simp only [morphism_distributive, x_l, x_r, List.take_append_drop]

      rw [TueMorseWord]
      rw [← x_break]
      rw [x_l_eq_y_l, x_r_eq_y_r]
      rw [y_r_eq_not_y_l]
      rw [← tue_morphism_inv_comm]
      rw [y_l_morph]
      rw [← ih]
      rw [TueMorseWordAlt]
      rw [ih]
      repeat simp
