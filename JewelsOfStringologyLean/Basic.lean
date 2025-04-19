import Mathlib.Tactic.Ring

variable { α: Type }

def period (w: List α) (p: Nat) := ∀ (i : Nat) (h: i + p < w.length), w[i] = w[i + p]

theorem period_0 (w: List α) : period w 0 := by
  rw [period]
  simp

-- aabaaabaa has period 4, 7, 8, 9
example : period [0, 0, 1, 0, 0, 0, 1, 0, 0] 4 := by rw [period]; simp_all +arith +decide
example : period [0, 0, 1, 0, 0, 0, 1, 0, 0] 7 := by rw [period]; simp_all +arith +decide
example : period [0, 0, 1, 0, 0, 0, 1, 0, 0] 8 := by rw [period]; simp_all +arith +decide
example : period [0, 0, 1, 0, 0, 0, 1, 0, 0] 9 := by rw [period]; simp_all +arith +decide

theorem period_drop (w: List α) (p: Nat) (hp: period w p) (d: Nat) : period (w.drop d) p := by
  rw [period]
  simp [List.drop_length] -- w[p..].length = w.length - p
  intro i hlen
  have di : d + i = i + d := by omega
  have dip : d + (i + p) = i + d + p := by omega
  simp_all
  rw [hp]

theorem period_take (w: List α) (p: Nat) (hp: period w p) (t: Nat) : period (w.take t) p := by
  rw [period]
  simp [List.take_length] -- w[..n].length = n
  intro i hlen
  rw [hp]

theorem gcd_diff (p q: Nat) (h: p ≤ q) : p.gcd q = (q-p).gcd p := by
  rw [Nat.gcd_comm (q-p) p] -- (q - p, p) = (p, q - p)
  rw [Nat.gcd_rec p (q-p)] -- (p, q - p) = ((q - p) % p, p)
  rw [Nat.gcd_rec p q] -- (p, q) = (q % p, p)
  rw [@Nat.mod_eq_sub_mod q p h] -- ((q - p) % p, p) = (q % p, p)

theorem gcd_le_diff (p q: Nat) (h: p < q) : q - p ≥ p.gcd q := by sorry

theorem fine_wilf_suffix_diff
  (w: List α) (p q: Nat)
  (hp: period w p) (hq: period w q) (h_p_le_q: p ≤ q) : period (w.drop p) (q - p) := by
  rw [period] -- rewrite period by definition
  simp [List.drop_length] -- w[p..].length = w.length - p
  intro i ht -- introduce variable for universal quantifier and assumption
  -- add few more facts for simpl_all to work properly
  have h_index : p + (i + (q - p)) = i + q := by omega
  have h_sum : p + i = i + p := by omega
  -- w[i + p] = w[i] = w[i + q]
  have h_sub_p : w[i + p] = w[i] := by rw [hp i]
  have h_sub_q : w[i + q] = w[i] := by rw [hq i]
  simp_all

theorem fine_wilf_suffix_div
  (w: List α) (p d: Nat)
  (hp: period w p) (hd: period (w.drop p) d) (hd: d ∣ p) (hlen: w.length ≥ 2 * p) : period w d := by
  sorry

-- Prod.lex constructs WellFounded relation - let's define it to simplify reasoning
def NatNatLT := (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)

-- proof that under WellFounded lexicographic relation (m - n, n) < (m, n)
lemma nat_nat_m_diff_n_1 (m n: Nat) (h₁: 0 < n) (h₂: n ≤ m) : NatNatLT.rel ((m - n), n) (m, n) := by
  have hmn : (m - n) < m := by omega
  exact @Prod.Lex.left Nat Nat Nat.lt Nat.lt (m - n) n m n hmn

-- proof that under WellFounded lexicographic relation (m, n - m) < (m, n)
lemma nat_nat_m_diff_n_2 (m n: Nat) (h₁: 0 < m) (h₂: m ≤ n) : NatNatLT.rel (m, n - m) (m, n) := by
  have hnm : (n - m) < n := by omega
  exact @Prod.Lex.right Nat Nat Nat.lt Nat.lt m (n - m) n hnm

theorem gcd_diff_induction
  (P : Nat×Nat → Prop)
  (m n : Nat)
  (Hcomm : ∀ m n, P (m, n) ↔ P (n, m))
  (H0 : ∀n, P (0, n))
  (H1 : ∀ m n, 0 < m → m ≤ n → P ((n - m), m) → P (m, n)) : P (m, n) := by
  induction (m, n) using @WellFounded.induction (Nat×Nat) NatNatLT.rel with
  | hwf => exact NatNatLT.wf
  | h x ih =>
    let (m, n) := x
    by_cases (m = 0)
    { simp_all }
    by_cases (n = 0)
    { simp_all }
    have m_pos : (0 < m) := by omega
    have n_pos : (0 < n) := by omega
    by_cases h_leq: (n ≤ m)
    {
      have P_m_diff_n : P ((m - n), n) := by
        apply ih
        apply nat_nat_m_diff_n_1
        exact n_pos
        trivial
      have P_n_m : P (n, m) := H1 n m n_pos h_leq P_m_diff_n
      simp_all [P_n_m]
    }
    by_cases h_gt: (n > m)
    {
      have h_leq : (m ≤ n) := by omega
      have n_geq_m : (n ≥ m) := by omega -- why we need this?
      have P_n_diff_m : P (m, (n - m)) := by
        apply ih
        apply nat_nat_m_diff_n_2
        exact m_pos
        trivial
      have P_n_diff_m_comm : P ((n - m), m) := by simp_all [Hcomm, P_n_diff_m]
      have P_m_n : P (m, n) := H1 m n m_pos h_leq P_n_diff_m_comm
      simp_all [P_m_n]
    }
    simp_all

def fine_wilf_prop (x: Nat×Nat) :=
  ∀ (w: List α), (period w x.fst) → (period w x.snd) → (w.length ≥ x.fst + x.snd - (x.fst.gcd x.snd)) → period w (x.fst.gcd x.snd)

lemma fine_wilf_zero (n: Nat) : @fine_wilf_prop α (0, n) := by sorry
lemma fine_wilf_comm (m n: Nat) : @fine_wilf_prop α (m, n) ↔ @fine_wilf_prop α (n, m) := by sorry

theorem fine_wilf (x: Nat×Nat) : @fine_wilf_prop α x := by
  apply gcd_diff_induction fine_wilf_prop x.fst x.snd fine_wilf_comm fine_wilf_zero
  intro p q h_p_pos h_p_le_q ih
  intro w h_p h_q h_len
  have h_len: w.length ≥ p + q - (p.gcd q) := by simp_all
  by_cases h_p_lt_q : (p < q)
  {
    have h_len_strong : w.length ≥ 2 * p := by
      calc w.length ≥ p + q - (p.gcd q) := h_len
           _ ≥ p + q - (q - p) := by
              apply Nat.sub_le_sub_left
              apply gcd_le_diff
              exact h_p_lt_q
           _ ≥ 2 * p := by omega
    have h_p : period w p := by simp_all
    have h_q : period w q := by simp_all
    have h_q_diff_p_suff : period (w.drop p) (q - p) := by
      apply fine_wilf_suffix_diff w p q h_p h_q h_p_le_q
    have h_p_suff : period (w.drop p) p := by
      apply period_drop w p h_p p
    have h_len_suff : (w.drop p).length ≥ (q - p) + p - (q - p).gcd p := by
      have gcd_comm : (q.gcd p) = (p.gcd q) := by rw [Nat.gcd_comm]
      simp_all [List.drop_length]
      omega
    have h_gcd_diff_suff : period (w.drop p) ((q - p).gcd p) := by
      apply ih (w.drop p) h_q_diff_p_suff h_p_suff h_len_suff
    have h_gcd_suff_qp : period (w.drop p) (q.gcd p) := by simp_all
    have h_gcd_suff_pq : period (w.drop p) (p.gcd q) := by simp_all [Nat.gcd_comm]
    have h_final : period w (p.gcd q) := by
      apply fine_wilf_suffix_div w p (p.gcd q) h_p h_gcd_suff_pq (Nat.gcd_dvd_left p q) h_len_strong
    exact h_final
  }
  by_cases h_p_eq_q : (p = q)
  { simp_all }
  omega

def hello := "Jewels of Stringology"
