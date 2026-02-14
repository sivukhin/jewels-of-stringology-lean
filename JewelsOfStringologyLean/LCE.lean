import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Log

/-! ## Cell-probe LCE lower bound formalization

We formalize key definitions and the proof structure from:
  "Tight Lower Bounds for the Longest Common Extension Problem" (Kosolobov)
which proves S(n) * T(n) = Ω(n log n) in the cell-probe model.

### Proof status
**Fully proven:**
- `ProbeTree.probes_le_depth` — depth bound implies probe count bound
- `ProbeTree.eval_eq_of_agree` — agreeing oracles yield same result
- `sumOracle_agree_of_string_agree` — shared encoding + string agreement → same eval
- `pigeonhole_encoding` — pigeonhole on encoding classes
- `counting_bound` — injection bound for identified subfamilies
- `family_card` — construction of the dictionary family
- `pigeonhole_probes` — pigeonhole on probe sets
- `lce_tradeoff` — chains the intermediate lemmas (main theorem)

**Remaining `sorry`:**
- `identifying_set` — core argument via LCE queries on block decomposition
-/

/-- A string of length `n` over a finite alphabet of size `σ`. -/
abbrev Str (σ n : Nat) := Fin n → Fin σ

/-- Encoding state: `S` cells each storing a value in `Fin n` (the word size). -/
abbrev State (S n : Nat) := Fin S → Fin n

/-- `lceExact s i j len` holds when `len` is the longest common extension of `s`
    starting at positions `i` and `j`: the first `len` characters match, and at
    position `len` either one index is out of bounds or the characters differ. -/
def lceExact {σ n : Nat} (s : Str σ n) (i j len : Nat) : Prop :=
  len ≤ n - i ∧
  len ≤ n - j ∧
  (∀ (m : Nat), m < len → (hi : i + m < n) → (hj : j + m < n) →
    s ⟨i + m, hi⟩ = s ⟨j + m, hj⟩) ∧
  (i + len ≥ n ∨ j + len ≥ n ∨
    ∃ (hi : i + len < n) (hj : j + len < n), s ⟨i + len, hi⟩ ≠ s ⟨j + len, hj⟩)

/-! ### Adaptive probe trees

A generic decision tree parameterized by a probe type `P` and a dependent response
family `R : P → Type`. Each node either returns a result or probes some `p : P`
and branches on the response `v : R p`. This models cell-probe access to multiple
arrays, each with its own index and value domain. -/

/-- An adaptive decision tree. `P` is the type of probes, `R p` is the response
    type for probe `p`. -/
inductive ProbeTree (P : Type) (R : P → Type) : Type where
  | answer : Nat → ProbeTree P R
  | probe : (p : P) → (R p → ProbeTree P R) → ProbeTree P R

/-- Evaluate a probe tree against an oracle. -/
def ProbeTree.eval {P : Type} {R : P → Type} :
    ProbeTree P R → ((p : P) → R p) → Nat
  | .answer v, _ => v
  | .probe p cont, oracle => (cont (oracle p)).eval oracle

/-- A probe tree has depth at most `d` (makes at most `d` probes on any input). -/
def ProbeTree.depthBounded {P : Type} {R : P → Type} :
    ProbeTree P R → Nat → Prop
  | .answer _, _ => True
  | .probe _ _, 0 => False
  | .probe p cont, d + 1 => ∀ v : R p, (cont v).depthBounded d

/-- The set of probes made when evaluating against a specific oracle. -/
def ProbeTree.probedPositions {P : Type} {R : P → Type} [DecidableEq P] :
    ProbeTree P R → ((p : P) → R p) → Finset P
  | .answer _, _ => ∅
  | .probe p cont, oracle => insert p ((cont (oracle p)).probedPositions oracle)

/-- A depth-bounded tree makes at most `d` probes on any oracle. -/
theorem ProbeTree.probes_le_depth {P : Type} {R : P → Type} [DecidableEq P]
    {t : ProbeTree P R} {d : Nat}
    (hd : t.depthBounded d) (oracle : (p : P) → R p) :
    (t.probedPositions oracle).card ≤ d := by
  induction t generalizing d with
  | answer _ => simp [probedPositions]
  | probe p cont ih =>
    cases d with
    | zero => exact hd.elim
    | succ d =>
      simp only [probedPositions]
      have h1 := Finset.card_insert_le p ((cont (oracle p)).probedPositions oracle)
      have h2 := ih (oracle p) (hd (oracle p))
      omega

/-- If two oracles agree on the probed positions, eval returns the same result. -/
theorem ProbeTree.eval_eq_of_agree {P : Type} {R : P → Type} [DecidableEq P]
    {t : ProbeTree P R} (oracle oracle' : (p : P) → R p)
    (h : ∀ p ∈ t.probedPositions oracle, oracle' p = oracle p) :
    t.eval oracle' = t.eval oracle := by
  induction t with
  | answer _ => rfl
  | probe p cont ih =>
    simp only [eval]
    have hp : oracle' p = oracle p := h p (Finset.mem_insert_self p _)
    rw [hp]
    exact ih (oracle p) (fun q hq => h q (Finset.mem_insert_of_mem hq))

/-! ### Sum-indexed oracles

Generic helpers for probe trees over a sum type `A ⊕ B`, where probes into the
left component return values of type `RA` and probes into the right return `RB`. -/

/-- Response type for a sum probe: left probes return `RA`, right probes return `RB`. -/
def SumResponse (RA RB : Type) : A ⊕ B → Type
  | .inl _ => RA
  | .inr _ => RB

/-- Build an oracle for a sum probe from two getters. -/
def sumOracle {A B RA RB : Type} (fa : A → RA) (fb : B → RB) :
    (p : A ⊕ B) → SumResponse RA RB p
  | .inl a => fa a
  | .inr b => fb b

/-! ### Cell-probe LCE data structure

The query algorithm accesses two arrays:
- **Encoding**: `S` cells, each storing a value in `Fin n` (the word size)
- **String**: `n` cells, each storing a value in `Fin σ` (the alphabet)

A probe is either `Sum.inl i` (read encoding cell `i : Fin S`) or
`Sum.inr j` (read string cell `j : Fin n`). -/

/-- A cell-probe LCE data structure over strings of length `n` with alphabet size `σ`.

    - `S` : number of encoding cells
    - `T` : maximum number of cell probes per query
    - `encode` : maps a string to a `State S n`
    - `queryTree` : for each pair of query positions, a fixed adaptive probe tree
    - `depthBound` : every query tree has depth at most `T`
    - `correct` : evaluating the query tree yields the exact LCE -/
structure CellProbeLCE (σ n : Nat) where
  S : Nat
  T : Nat
  encode : Str σ n → State S n
  queryTree : Nat → Nat → ProbeTree (Fin S ⊕ Fin n) (SumResponse (Fin n) (Fin σ))
  depthBound : ∀ (i j : Nat), (queryTree i j).depthBounded T
  correct : ∀ (s : Str σ n) (i j : Nat), lceExact s i j ((queryTree i j).eval (sumOracle (encode s) s))

/-- The `p`-th block of length `k` in string `s`, i.e., `s[p*k .. (p+1)*k - 1]`. -/
def nthBlock {σ n : Nat} (s : Str σ n) (k : Nat) (p : Nat) : Fin k → Option (Fin σ) :=
  fun ⟨i, _⟩ =>
    if h : p * k + i < n then some (s ⟨p * k + i, h⟩) else none

/-- A string `s` has a *dictionary prefix* of block-length `k` if the first `σ^k` blocks
    of length `k` enumerate all possible strings of length `k` over `Fin σ`. -/
def hasDictPrefix {σ n : Nat} (s : Str σ n) (k : Nat) : Prop :=
  σ ^ k * k ≤ n ∧
  ∀ (w : Fin k → Fin σ), ∃ (p : Fin (σ ^ k)),
    ∀ (i : Fin k), (hi : p.val * k + i.val < n) →
      s ⟨p.val * k + i.val, hi⟩ = w i

/-- The family of strings with a dictionary prefix of block-length `k`. -/
def DictFamily (σ n k : Nat) : Set (Str σ n) :=
  { s | hasDictPrefix s k }

/-! ### Key lemmas -/

/-- The dictionary family has at least `σ^(n/2)` elements, because the tail
    (positions after the dictionary prefix) can be any string of length ≥ n/2. -/
theorem family_card {σ n k : Nat}
    (hσ : σ ≥ 2) (hk : k ≥ 1) (hn : 2 * σ ^ k * k ≤ n) :
    ∃ (F : Finset (Str σ n)),
      (↑F : Set (Str σ n)) ⊆ DictFamily σ n k ∧
      F.card ≥ σ ^ (n / 2) ∧
      (∀ s ∈ F, ∀ s' ∈ F, ∀ (i : Fin n), i.val < σ ^ k * k → s i = s' i) := by
  classical
  have hpk : σ ^ k * k ≤ n :=
    le_trans (Nat.mul_le_mul_right k (by omega : σ ^ k ≤ 2 * σ ^ k)) hn
  have hk_pos : k > 0 := by omega
  -- Bijection between k-strings and Fin (σ^k)
  have hce : Fintype.card (Fin k → Fin σ) = σ ^ k := by
    simp [Fintype.card_fun, Fintype.card_fin]
  let toWord : Fin (σ ^ k) → (Fin k → Fin σ) :=
    (Fintype.equivFin (Fin k → Fin σ)).symm ∘ (finCongr hce.symm)
  let toIdx : (Fin k → Fin σ) → Fin (σ ^ k) :=
    (finCongr hce) ∘ (Fintype.equivFin (Fin k → Fin σ))
  have h_inv : ∀ w, toWord (toIdx w) = w := by
    intro w; simp [toWord, toIdx]
  -- Build strings: fixed dictionary prefix + arbitrary tail
  let mkStr : (Fin (n - σ ^ k * k) → Fin σ) → Str σ n := fun t ⟨i, hi⟩ =>
    if h : i < σ ^ k * k then
      toWord ⟨i / k, (Nat.div_lt_iff_lt_mul hk_pos).mpr h⟩ ⟨i % k, Nat.mod_lt i hk_pos⟩
    else
      t ⟨i - σ ^ k * k, by omega⟩
  have h_inj : Function.Injective mkStr := by
    intro t₁ t₂ heq; funext ⟨i, hi⟩
    have := congr_fun heq ⟨σ ^ k * k + i, by omega⟩
    simp only [mkStr, show ¬(σ ^ k * k + i < σ ^ k * k) from by omega, ↓reduceDIte,
               show σ ^ k * k + i - σ ^ k * k = i from by omega] at this
    exact this
  refine ⟨Finset.univ.image mkStr, ?_, ?_, ?_⟩
  · -- F ⊆ DictFamily
    intro s hs
    simp only [Finset.mem_coe, Finset.mem_image] at hs
    obtain ⟨t, _, rfl⟩ := hs
    refine ⟨hpk, fun w => ⟨toIdx w, fun ⟨i, hi_k⟩ hi_n => ?_⟩⟩
    have h_in_pref : (toIdx w).val * k + i < σ ^ k * k :=
      calc (toIdx w).val * k + i
          < (toIdx w).val * k + k := by omega
        _ = ((toIdx w).val + 1) * k := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ σ ^ k * k := Nat.mul_le_mul_right k (by omega)
    simp only [mkStr, h_in_pref, ↓reduceDIte]
    have h_div : ((toIdx w).val * k + i) / k = (toIdx w).val := by
      rw [show (toIdx w).val * k + i = k * (toIdx w).val + i from by rw [Nat.mul_comm]]
      rw [Nat.mul_add_div hk_pos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    have h_mod : ((toIdx w).val * k + i) % k = i := by
      rw [show (toIdx w).val * k + i = k * (toIdx w).val + i from by rw [Nat.mul_comm]]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have key := congr_fun (h_inv w) ⟨i, hi_k⟩
    simp only [Function.comp] at key
    convert key using 2 <;> exact Fin.ext (by assumption)
  · -- F.card ≥ σ^(n/2)
    calc (Finset.univ.image mkStr).card
        = Fintype.card (Fin (n - σ ^ k * k) → Fin σ) := by
          rw [Finset.card_image_of_injective _ h_inj, Finset.card_univ]
      _ = σ ^ (n - σ ^ k * k) := by simp [Fintype.card_fun, Fintype.card_fin]
      _ ≥ σ ^ (n / 2) := by
          apply Nat.pow_le_pow_right (by omega : 0 < σ)
          have h_assoc : 2 * σ ^ k * k = 2 * (σ ^ k * k) := Nat.mul_assoc 2 (σ ^ k) k
          omega
  · -- Shared dictionary prefix: all strings in F agree on the first σ^k*k positions
    intro s hs s' hs' ⟨i, _⟩ hi_pref
    simp only [Finset.mem_image] at hs hs'
    obtain ⟨t, _, rfl⟩ := hs
    obtain ⟨t', _, rfl⟩ := hs'
    simp only [mkStr, hi_pref, ↓reduceDIte]

/-- Pigeonhole on encodings: there exists an encoding class (strings sharing the
    same encoding) of size at least `|F| / n^S`. Each encoding is a `State S n`,
    giving at most `n^S` distinct encodings. -/
theorem pigeonhole_encoding {σ n k : Nat}
    (A : CellProbeLCE σ n)
    (F : Finset (Str σ n))
    (hF : (↑F : Set (Str σ n)) ⊆ DictFamily σ n k) :
    ∃ (I : Finset (Str σ n)),
      (↑I : Set (Str σ n)) ⊆ ↑F ∧
      I.card ≥ F.card / n ^ A.S ∧
      ∀ s ∈ I, ∀ s' ∈ I, A.encode s = A.encode s' := by
  classical
  by_cases hn0 : n ^ A.S = 0
  · -- Degenerate case: n^S = 0, so F.card / 0 = 0
    exact ⟨∅, by simp, by simp [hn0], fun _ h => absurd h (Finset.not_mem_empty _)⟩
  · -- n^S > 0, so State A.S n is nonempty
    have h_pos : n ^ A.S > 0 := Nat.pos_of_ne_zero hn0
    have h_card_enc : Fintype.card (State A.S n) = n ^ A.S := by
      simp [Fintype.card_fun, Fintype.card_fin]
    haveI : Nonempty (State A.S n) :=
      Fintype.card_pos_iff.mp (by omega)
    -- Apply pigeonhole: among ≤ n^S encodings, some fiber has ≥ |F|/n^S strings
    obtain ⟨c, _, hc⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (f := A.encode) (s := F) (t := Finset.univ) (n := F.card / n ^ A.S)
      (fun _ _ => Finset.mem_univ _)
      Finset.univ_nonempty
      (by rw [Finset.card_univ, h_card_enc]
          exact le_of_eq (Nat.mul_comm ..) |>.trans (Nat.div_mul_le_self F.card (n ^ A.S)))
    refine ⟨F.filter (fun s => A.encode s = c), ?_, hc, ?_⟩
    · intro x hx; exact Finset.mem_coe.mpr ((Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1)
    · intro s hs s' hs'
      exact ((Finset.mem_filter.mp hs).2).trans ((Finset.mem_filter.mp hs').2).symm

/-- Extract the string-cell probes (right components) from a set of sum-typed probes. -/
def stringProbesOf {S n : Nat} (probes : Finset (Fin S ⊕ Fin n)) : Finset (Fin n) :=
  probes.biUnion (fun p => match p with | .inr j => {j} | .inl _ => ∅)

/-- If two strings share encoding and agree on all string probes, the sum oracles
    agree on the probed positions. This is the key link between ProbeTree and LCE. -/
theorem sumOracle_agree_of_string_agree {S σ n : Nat}
    {t : ProbeTree (Fin S ⊕ Fin n) (SumResponse (Fin n) (Fin σ))}
    (e : State S n) (s s' : Str σ n)
    (h : ∀ j ∈ stringProbesOf (t.probedPositions (sumOracle e s)),
         s' j = s j) :
    t.eval (sumOracle e s') = t.eval (sumOracle e s) := by
  apply ProbeTree.eval_eq_of_agree
  intro p hp
  match p with
  | .inl i => rfl
  | .inr j => exact h j (Finset.mem_biUnion.mpr ⟨.inr j, hp, Finset.mem_singleton_self j⟩)

/-- For each string in the encoding class, there is an identifying set of
    *string* positions of size at most `T * n / k`. Since all strings in
    the class share the same encoding, the query trees read identical values
    from encoding cells — only string cell probes distinguish strings. -/
theorem identifying_set {σ n k : Nat}
    (A : CellProbeLCE σ n)
    (I : Finset (Str σ n))
    (hI_enc : ∀ s ∈ I, ∀ s' ∈ I, A.encode s = A.encode s')
    (hDict : (↑I : Set (Str σ n)) ⊆ DictFamily σ n k)
    (hShared : ∀ s ∈ I, ∀ s' ∈ I, ∀ (i : Fin n), i.val < σ ^ k * k → s i = s' i)
    (hk : k ≥ 1) :
    ∀ s ∈ I, ∃ (Ts : Finset (Fin n)),
      Ts.card ≤ A.T * n / k ∧
      ∀ s' ∈ I, (∀ p ∈ Ts, s' p = s p) → s' = s := by sorry

/-- Pigeonhole on probe sets: there is a subfamily sharing the same probe set.
    Uses `identifying_set` to get per-string identifying sets, then pigeonholes
    on the ≤ 2^n subsets of [0..n-1] to find a common one. -/
theorem pigeonhole_probes {σ n k : Nat}
    (A : CellProbeLCE σ n)
    (I : Finset (Str σ n))
    (hI_enc : ∀ s ∈ I, ∀ s' ∈ I, A.encode s = A.encode s')
    (hDict : (↑I : Set (Str σ n)) ⊆ DictFamily σ n k)
    (hShared : ∀ s ∈ I, ∀ s' ∈ I, ∀ (i : Fin n), i.val < σ ^ k * k → s i = s' i)
    (hk : k ≥ 1) :
    ∃ (I' : Finset (Str σ n)) (T_common : Finset (Fin n)),
      (↑I' : Set (Str σ n)) ⊆ ↑I ∧
      I'.card ≥ I.card / 2 ^ n ∧
      T_common.card ≤ A.T * n / k ∧
      ∀ s ∈ I', ∀ s' ∈ I', (∀ p ∈ T_common, s' p = s p) → s' = s := by
  classical
  have hident := identifying_set A I hI_enc hDict hShared hk
  by_cases hI_empty : I = ∅
  · exact ⟨∅, ∅, by simp, by simp [hI_empty], by simp,
      fun _ h => absurd h (Finset.not_mem_empty _)⟩
  · -- For each s ∈ I, choose an identifying set (non-dependent function)
    let f : Str σ n → Finset (Fin n) := fun s =>
      if hs : s ∈ I then (hident s hs).choose else ∅
    have hf_prop : ∀ s (hs : s ∈ I),
        (f s).card ≤ A.T * n / k ∧
        ∀ s' ∈ I, (∀ p ∈ f s, s' p = s p) → s' = s := by
      intro s hs; have : f s = (hident s hs).choose := dif_pos hs
      rw [this]; exact (hident s hs).choose_spec
    -- Pigeonhole: among ≤ 2^n subsets of Fin n, some fiber has ≥ |I|/2^n strings
    have h_card_sets : Fintype.card (Finset (Fin n)) = 2 ^ n := by
      rw [Fintype.card_finset, Fintype.card_fin]
    obtain ⟨T, _, hT_card⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (f := f) (s := I) (t := Finset.univ) (n := I.card / 2 ^ n)
      (fun _ _ => Finset.mem_univ _)
      Finset.univ_nonempty
      (by rw [Finset.card_univ, h_card_sets]
          exact le_of_eq (Nat.mul_comm ..) |>.trans (Nat.div_mul_le_self I.card (2 ^ n)))
    -- I' is the fiber: strings in I with identifying set T
    by_cases hI'_empty : (I.filter (fun s => f s = T)) = ∅
    · -- Empty fiber ⟹ I.card / 2^n = 0
      refine ⟨∅, ∅, by simp, ?_, by simp, fun _ h => absurd h (Finset.not_mem_empty _)⟩
      have : (I.filter (fun s => f s = T)).card = 0 := by rw [hI'_empty]; simp
      omega
    · -- Nonempty fiber — get witness for T's cardinality bound
      obtain ⟨s₀, hs₀⟩ := Finset.nonempty_of_ne_empty hI'_empty
      have hs₀_I := (Finset.mem_filter.mp hs₀).1
      have hs₀_f : f s₀ = T := (Finset.mem_filter.mp hs₀).2
      refine ⟨I.filter (fun s => f s = T), T, ?_, hT_card, ?_, ?_⟩
      · intro x hx
        exact Finset.mem_coe.mpr ((Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1)
      · -- T.card ≤ A.T * n / k (via witness s₀)
        rw [← hs₀_f]; exact (hf_prop s₀ hs₀_I).1
      · -- Identification property
        intro s hs s' hs' hagree
        have hs_I := (Finset.mem_filter.mp hs).1
        have hs_f : f s = T := (Finset.mem_filter.mp hs).2
        exact (hf_prop s hs_I).2 s' ((Finset.mem_filter.mp hs').1)
          (fun p hp => hagree p (hs_f ▸ hp))

/-- Counting bound: a subfamily identified by a common probe set of size `m`
    has at most `σ^m` elements. -/
theorem counting_bound {σ n : Nat}
    (I' : Finset (Str σ n))
    (T_common : Finset (Fin n))
    (hident : ∀ s ∈ I', ∀ s' ∈ I', (∀ p ∈ T_common, s' p = s p) → s' = s) :
    I'.card ≤ σ ^ T_common.card := by
  classical
  -- Restrict each string to T_common positions
  let f : Str σ n → (↥T_common → Fin σ) := fun s p => s p.val
  -- f is injective on I'
  have hf : Set.InjOn f ↑I' := by
    intro s hs s' hs' heq
    exact (hident s hs s' hs' (fun p hp => (congr_fun heq ⟨p, hp⟩).symm)).symm
  calc I'.card
      = (I'.image f).card := (Finset.card_image_of_injOn hf).symm
    _ ≤ Fintype.card (↥T_common → Fin σ) := Finset.card_le_univ _
    _ = σ ^ T_common.card := by
        rw [Fintype.card_fun, Fintype.card_fin,
            Fintype.card_of_subtype T_common (fun _ => Iff.rfl)]

/-- **Main theorem (finite version).**
    For any cell-probe LCE data structure over an alphabet of size `σ` on strings
    of length `n` with dictionary-prefix parameter `k`, if the space satisfies
    `n^S * 2^n ≤ σ^(n/4)` (encoding count × subset count ≤ σ^(n/4)),
    then `4 * T ≥ k`. This captures the `S * T = Ω(n log n)` trade-off. -/
theorem lce_tradeoff {σ n k : Nat}
    (hσ : σ ≥ 2) (hk : k ≥ 1) (hn : 2 * σ ^ k * k ≤ n)
    (A : CellProbeLCE σ n) (hS : n ^ A.S * 2 ^ n ≤ σ ^ (n / 4)) :
    4 * A.T ≥ k := by
  -- Step 1: Construct the dictionary family
  obtain ⟨F, hF_sub, hF_card, hF_shared⟩ := family_card hσ hk hn
  -- Step 2: Pigeonhole on encodings — find encoding class I ⊆ F
  obtain ⟨I, hI_sub, hI_card, hI_enc⟩ := pigeonhole_encoding A F hF_sub
  -- Derive properties of I from F
  have hI_dict : (↑I : Set (Str σ n)) ⊆ DictFamily σ n k :=
    Set.Subset.trans (by exact_mod_cast hI_sub) hF_sub
  have hI_shared : ∀ s ∈ I, ∀ s' ∈ I, ∀ (i : Fin n), i.val < σ ^ k * k → s i = s' i :=
    fun s hs s' hs' i hi => hF_shared s (hI_sub hs) s' (hI_sub hs') i hi
  -- Step 3: Pigeonhole on probe sets
  obtain ⟨I', T_common, hI'_sub, hI'_card, hT_card, hI'_ident⟩ :=
    pigeonhole_probes (k := k) A I hI_enc hI_dict hI_shared hk
  -- Step 4: Counting bound
  have hcount := counting_bound I' T_common hI'_ident
  -- Step 5: Derive I'.card ≥ σ^(n/4)
  -- Chain: I'.card ≥ I.card / 2^n ≥ (F.card / n^S) / 2^n ≥ σ^(n/2) / (n^S * 2^n)
  --        ≥ σ^(n/2) / σ^(n/4) = σ^(n/2 - n/4) ≥ σ^(n/4)
  have hσ_pos : 0 < σ := by omega
  have hsk_pos : σ ^ k ≥ 1 := Nat.one_le_pow k σ (by omega)
  have hn_pos : 0 < n := by
    have : 2 * σ ^ k * k ≥ 2 * 1 * 1 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hsk_pos) hk
    omega
  have hn4 : n / 2 - n / 4 ≥ n / 4 := by omega
  have hpow_split : σ ^ (n / 2) = σ ^ (n / 4) * σ ^ (n / 2 - n / 4) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hI'_lower : I'.card ≥ σ ^ (n / 4) := by
    have h1 : I.card ≥ σ ^ (n / 2) / n ^ A.S :=
      le_trans (Nat.div_le_div_right hF_card) hI_card
    have h2 : I'.card ≥ σ ^ (n / 2) / (n ^ A.S * 2 ^ n) := by
      calc I'.card
          ≥ I.card / 2 ^ n := hI'_card
        _ ≥ (σ ^ (n / 2) / n ^ A.S) / 2 ^ n := Nat.div_le_div_right h1
        _ = σ ^ (n / 2) / (n ^ A.S * 2 ^ n) := by rw [Nat.div_div_eq_div_mul]
    calc I'.card
        ≥ σ ^ (n / 2) / (n ^ A.S * 2 ^ n) := h2
      _ ≥ σ ^ (n / 2) / σ ^ (n / 4) := by
          apply Nat.div_le_div_left hS
          exact Nat.mul_pos (Nat.pow_pos hn_pos) (Nat.pow_pos (by omega : 0 < 2))
      _ = σ ^ (n / 2 - n / 4) := by
          rw [hpow_split, Nat.mul_div_cancel_left _ (Nat.pow_pos hσ_pos)]
      _ ≥ σ ^ (n / 4) := Nat.pow_le_pow_right hσ_pos hn4
  -- Step 6: Derive 4*T ≥ k by contradiction
  -- From hcount and hI'_lower: σ^(T_common.card) ≥ σ^(n/4)
  -- Hence T_common.card ≥ n/4. With T_common.card ≤ T*n/k: T*n/k ≥ n/4.
  by_contra h_neg
  push_neg at h_neg  -- h_neg : 4 * A.T < k, i.e., k ≥ 4*A.T + 1
  -- From hcount and hI'_lower: σ^(T_common.card) ≥ σ^(n/4)
  have hT_ge : T_common.card ≥ n / 4 := by
    by_contra h_lt; push_neg at h_lt
    have : σ ^ T_common.card < σ ^ (n / 4) :=
      Nat.pow_lt_pow_right (by omega : σ > 1) h_lt
    omega  -- I'.card ≤ σ^T_common.card < σ^(n/4) ≤ I'.card
  -- n/4 ≤ T_common.card ≤ A.T * n / k
  have h_chain : n / 4 ≤ A.T * n / k := le_trans hT_ge hT_card
  -- By Nat.le_div_iff_mul_le: (n/4) * k ≤ A.T * n
  have h_mul : (n / 4) * k ≤ A.T * n :=
    (Nat.le_div_iff_mul_le (by omega : k > 0)).mp h_chain
  -- From hn: n ≥ 2*σ^k*k ≥ 4*k (since σ^k ≥ 2)
  have hsk : σ ^ k ≥ 2 := by
    calc (2 : Nat) = 2 ^ 1 := (Nat.pow_one 2).symm
         _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
         _ ≤ σ ^ k := Nat.pow_le_pow_left (by omega) k
  have hn_ge : n ≥ 4 * k := by
    have := Nat.mul_le_mul_right k (show 2 * σ ^ k ≥ 4 by omega)
    omega
  -- Since k ≥ 4*A.T + 1, n ≥ 4*k ≥ 4*(4*A.T + 1) = 16*A.T + 4
  have hn_ge2 : n ≥ 16 * A.T + 4 := by
    have : k ≥ 4 * A.T + 1 := by omega
    have : 4 * k ≥ 4 * (4 * A.T + 1) := Nat.mul_le_mul_left 4 this
    omega
  -- n/4 ≥ 4*A.T + 1
  have hn4_ge : n / 4 ≥ 4 * A.T + 1 := by omega
  -- But from h_mul: (n/4)*k ≤ A.T*n
  -- (n/4)*(4*A.T + 1) ≤ (n/4)*k ≤ A.T*n
  -- 4*A.T*(n/4) + n/4 ≤ A.T*n
  -- n/4 ≤ A.T*(n - 4*(n/4)) = A.T*(n%4) ≤ 3*A.T
  have h_mod : n / 4 ≤ 3 * A.T := by
    have h_expand : (n / 4) * (4 * A.T + 1) ≤ A.T * n := by
      calc (n / 4) * (4 * A.T + 1)
          ≤ (n / 4) * k := Nat.mul_le_mul_left _ (by omega)
        _ ≤ A.T * n := h_mul
    have h_distrib : (n / 4) * (4 * A.T + 1) = (n / 4) * (4 * A.T) + n / 4 := by
      rw [Nat.mul_add, Nat.mul_one]
    have h_mul_upper : A.T * n ≤ A.T * (4 * (n / 4) + 3) :=
      Nat.mul_le_mul_left _ (by omega)
    have h_distrib2 : A.T * (4 * (n / 4) + 3) = A.T * (4 * (n / 4)) + A.T * 3 :=
      Nat.mul_add ..
    have h_comm : (n / 4) * (4 * A.T) = A.T * (4 * (n / 4)) := by
      rw [Nat.mul_comm (n / 4) (4 * A.T), Nat.mul_assoc, Nat.mul_comm A.T (n / 4),
          ← Nat.mul_assoc, Nat.mul_comm (4 * (n / 4)) A.T]
    have step1 : A.T * (4 * (n / 4)) + n / 4 ≤ A.T * n := by
      rw [← h_comm, ← h_distrib]; exact h_expand
    have step2 : A.T * n ≤ A.T * (4 * (n / 4)) + A.T * 3 := by
      rw [← h_distrib2]; exact h_mul_upper
    have := Nat.le_of_add_le_add_left (le_trans step1 step2)
    omega
  -- Contradiction: 4*A.T + 1 ≤ n/4 ≤ 3*A.T ⟹ A.T + 1 ≤ 0
  omega
