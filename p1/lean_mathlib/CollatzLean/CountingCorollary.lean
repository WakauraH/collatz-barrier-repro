import Mathlib

/-!
CountingCorollary.lean — the combinatorial core of the counting corollary of P1
(Corollary "counting potential counterexamples"), formalized against Mathlib.

T is the compressed Collatz map.  For M = 2^m and n ∈ (M, 2M] whose first m iterates
all stay ≥ n (this contains every n ∈ (M,2M] whose orbit never descends below n),
let e = odds n m be the number of odd steps among the first m steps.  Then

  (growth)     2^(m·(e+1)) ≤ (3·2^m + 1)^e,
               i.e.  e ≥ m·θ_M with θ_M = log 2 / log(3 + 2^{-m});

  (injective)  n ↦ {i < m : T^i n odd} is injective on (M, 2M]     (Terras);

  (count)      #{n ∈ (M,2M] : stays m n} ≤ Σ_{e ≤ m, 2^(m(e+1)) ≤ (3·2^m+1)^e} C(m, e).

The entropy estimate Σ_{e ≥ pm} C(m,e) ≤ 2^{mH(p)} (p ≥ 1/2) and the translation of the
integer inequality into e ≥ mθ_M are left to the text (elementary calculus).
-/

open Finset

namespace CollatzCount

/-- The compressed Collatz map. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

lemma two_mul_T_even {n : ℕ} (h : n % 2 = 0) : 2 * T n = n := by
  unfold T; rw [if_pos h]; omega

lemma two_mul_T_odd {n : ℕ} (h : n % 2 = 1) : 2 * T n = 3 * n + 1 := by
  unfold T; rw [if_neg (by omega)]; omega

/-- number of odd steps among the first `j` iterates (positions 0, …, j-1). -/
def odds (n j : ℕ) : ℕ := ∑ i ∈ range j, T^[i] n % 2

lemma odds_succ (n j : ℕ) : odds n (j + 1) = odds n j + T^[j] n % 2 := by
  unfold odds; rw [sum_range_succ]

/-- the set of odd positions among the first `m` steps. -/
def parityset (n m : ℕ) : Finset ℕ := (range m).filter (fun i => T^[i] n % 2 = 1)

lemma card_parityset (n m : ℕ) : (parityset n m).card = odds n m := by
  unfold parityset odds
  rw [card_filter]
  apply sum_congr rfl
  intro i _
  have := Nat.mod_two_eq_zero_or_one (T^[i] n)
  rcases this with h | h <;> simp [h]

/-- the first `m` iterates all stay at or above `n`. -/
def stays (m n : ℕ) : Prop := ∀ j ≤ m, n ≤ T^[j] n

instance (m : ℕ) : DecidablePred (stays m) := fun n => by unfold stays; infer_instance

/-! ### Growth: the integer form of e ≥ m θ_M -/

lemma growth (m n : ℕ) (hn : 2 ^ m ≤ n) (hs : stays m n) :
    ∀ j ≤ m, 2 ^ (j + m * odds n j) * T^[j] n ≤ (3 * 2 ^ m + 1) ^ (odds n j) * n := by
  intro j
  induction j with
  | zero => intro _; simp [odds]
  | succ j ih =>
    intro hj
    have ih' := ih (by omega)
    have hx : 2 ^ m ≤ T^[j] n := le_trans hn (hs j (by omega))
    rw [Function.iterate_succ_apply', odds_succ]
    set x := T^[j] n with hxdef
    set e := odds n j
    have hpos : 0 < 2 ^ (j + m * e) := by positivity
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · -- even step: 2 T x = x
      have h2 := two_mul_T_even h
      rw [h]
      calc 2 ^ (j + 1 + m * (e + 0)) * T x
          = 2 ^ (j + m * e) * (2 * T x) := by ring
        _ = 2 ^ (j + m * e) * x := by rw [h2]
        _ ≤ (3 * 2 ^ m + 1) ^ e * n := ih'
    · -- odd step: 2 T x = 3x + 1 and 2^m (3x+1) ≤ (3·2^m+1) x since 2^m ≤ x
      have h2 := two_mul_T_odd h
      rw [h]
      have key : 2 ^ m * (3 * x + 1) ≤ (3 * 2 ^ m + 1) * x := by nlinarith
      calc 2 ^ (j + 1 + m * (e + 1)) * T x
          = 2 ^ (j + m * e) * (2 ^ m * (2 * T x)) := by ring
        _ = 2 ^ (j + m * e) * (2 ^ m * (3 * x + 1)) := by rw [h2]
        _ ≤ 2 ^ (j + m * e) * ((3 * 2 ^ m + 1) * x) := Nat.mul_le_mul_left _ key
        _ = (3 * 2 ^ m + 1) * (2 ^ (j + m * e) * x) := by ring
        _ ≤ (3 * 2 ^ m + 1) * ((3 * 2 ^ m + 1) ^ e * n) := Nat.mul_le_mul_left _ ih'
        _ = (3 * 2 ^ m + 1) ^ (e + 1) * n := by ring

/-- **Growth inequality.** If n > 2^m and the first m iterates stay ≥ n, then
    2^(m(e+1)) ≤ (3·2^m+1)^e with e the number of odd steps among the first m. -/
theorem growth_ineq (m n : ℕ) (hn : 2 ^ m < n) (hs : stays m n) :
    2 ^ (m * (odds n m + 1)) ≤ (3 * 2 ^ m + 1) ^ (odds n m) := by
  have h := growth m n hn.le hs m le_rfl
  have hstay := hs m le_rfl
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
  have h1 : 2 ^ (m + m * odds n m) * n ≤ (3 * 2 ^ m + 1) ^ (odds n m) * n :=
    le_trans (Nat.mul_le_mul_left _ hstay) h
  have h2 : 2 ^ (m + m * odds n m) ≤ (3 * 2 ^ m + 1) ^ (odds n m) :=
    Nat.le_of_mul_le_mul_right h1 hnpos
  have : m * (odds n m + 1) = m + m * odds n m := by ring
  rw [this]; exact h2

/-! ### Injectivity of the parity vector on (M, 2M] (Terras) -/

lemma diff_step (x x' : ℕ) (h : x % 2 = x' % 2) :
    (2 : ℤ) * ((T x : ℤ) - T x') = (if x % 2 = 1 then 3 else 1) * ((x : ℤ) - x') := by
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx
  · have hx' : x' % 2 = 0 := by omega
    have a := two_mul_T_even hx; have b := two_mul_T_even hx'
    rw [if_neg (by omega)]
    have a' : (2 : ℤ) * T x = x := by exact_mod_cast a
    have b' : (2 : ℤ) * T x' = x' := by exact_mod_cast b
    linarith
  · have hx' : x' % 2 = 1 := by omega
    have a := two_mul_T_odd hx; have b := two_mul_T_odd hx'
    rw [if_pos hx]
    have a' : (2 : ℤ) * T x = 3 * x + 1 := by exact_mod_cast a
    have b' : (2 : ℤ) * T x' = 3 * x' + 1 := by exact_mod_cast b
    linarith

/-- affine difference identity: with the same first j parities,
    2^j (T^j n − T^j n') = 3^{e_j} (n − n'). -/
lemma diff_iter (n n' : ℕ) :
    ∀ j, (∀ i < j, T^[i] n % 2 = T^[i] n' % 2) →
      (2 : ℤ) ^ j * ((T^[j] n : ℤ) - T^[j] n') = 3 ^ (odds n j) * ((n : ℤ) - n') := by
  intro j
  induction j with
  | zero => intro _; simp [odds]
  | succ j ih =>
    intro hp
    have ih' := ih (fun i hi => hp i (by omega))
    have hj := hp j (by omega)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', odds_succ]
    have hd := diff_step (T^[j] n) (T^[j] n') hj
    rcases Nat.mod_two_eq_zero_or_one (T^[j] n) with h | h
    · rw [if_neg (by omega)] at hd
      rw [h, Nat.add_zero, pow_succ]
      calc (2 : ℤ) ^ j * 2 * ((T (T^[j] n) : ℤ) - T (T^[j] n'))
          = 2 ^ j * (2 * ((T (T^[j] n) : ℤ) - T (T^[j] n'))) := by ring
        _ = 2 ^ j * (1 * ((T^[j] n : ℤ) - T^[j] n')) := by rw [hd]
        _ = 3 ^ odds n j * ((n : ℤ) - n') := by rw [one_mul, ih']
    · rw [if_pos h] at hd
      rw [h, pow_succ, pow_succ]
      calc (2 : ℤ) ^ j * 2 * ((T (T^[j] n) : ℤ) - T (T^[j] n'))
          = 2 ^ j * (2 * ((T (T^[j] n) : ℤ) - T (T^[j] n'))) := by ring
        _ = 2 ^ j * (3 * ((T^[j] n : ℤ) - T^[j] n')) := by rw [hd]
        _ = 3 * (2 ^ j * ((T^[j] n : ℤ) - T^[j] n')) := by ring
        _ = 3 ^ odds n j * 3 * ((n : ℤ) - n') := by rw [ih']; ring

lemma two_dvd_pow_dvd (n n' : ℕ) :
    ∀ j, (∀ i < j, T^[i] n % 2 = T^[i] n' % 2) → (2 : ℤ) ^ j ∣ (n : ℤ) - n' := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hp
    obtain ⟨d, hd⟩ := ih (fun i hi => hp i (by omega))
    have hj := hp j (by omega)
    have hdi := diff_iter n n' j (fun i hi => hp i (by omega))
    rw [hd] at hdi
    -- T^j n − T^j n' = 3^e d
    have hpos : (0 : ℤ) < 2 ^ j := by positivity
    have h1 : ((T^[j] n : ℤ) - T^[j] n') = 3 ^ odds n j * d := by
      have : (2 : ℤ) ^ j * ((T^[j] n : ℤ) - T^[j] n') = 2 ^ j * (3 ^ odds n j * d) := by
        rw [hdi]; ring
      exact mul_left_cancel₀ hpos.ne' this
    -- same parity at j ⇒ the difference is even
    have heven : (2 : ℤ) ∣ (T^[j] n : ℤ) - T^[j] n' := by
      have := Int.emod_emod_of_dvd (T^[j] n : ℤ) (by norm_num : (2 : ℤ) ∣ 2)
      have hn2 : ((T^[j] n : ℤ) % 2) = ((T^[j] n' : ℤ) % 2) := by
        have a : ((T^[j] n : ℤ) % 2) = ((T^[j] n % 2 : ℕ) : ℤ) := by push_cast; rfl
        have b : ((T^[j] n' : ℤ) % 2) = ((T^[j] n' % 2 : ℕ) : ℤ) := by push_cast; rfl
        rw [a, b, hj]
      exact Int.ModEq.dvd hn2.symm
    rw [h1] at heven
    have hodd : ¬ (2 : ℤ) ∣ 3 ^ odds n j := by
      intro h
      have := Int.Prime.dvd_pow' (by norm_num : Nat.Prime 2) h
      norm_num at this
    have hd2 : (2 : ℤ) ∣ d := (Int.Prime.dvd_mul' (by norm_num : Nat.Prime 2) heven).resolve_left hodd
    obtain ⟨d', hd'⟩ := hd2
    exact ⟨d', by rw [hd, hd']; ring⟩

lemma parity_of_parityset {n n' m : ℕ} (h : parityset n m = parityset n' m) :
    ∀ i < m, T^[i] n % 2 = T^[i] n' % 2 := by
  intro i hi
  have key : (i ∈ parityset n m) ↔ (i ∈ parityset n' m) := by rw [h]
  simp only [parityset, mem_filter, mem_range] at key
  have := Nat.mod_two_eq_zero_or_one (T^[i] n)
  have := Nat.mod_two_eq_zero_or_one (T^[i] n')
  omega

/-- **Terras injectivity**: on (2^m, 2^(m+1)] the parity set of the first m steps
    determines n. -/
theorem parityset_injective (m : ℕ) :
    Set.InjOn (fun n => parityset n m) (Ioc (2 ^ m) (2 ^ (m + 1)) : Finset ℕ) := by
  intro n hn n' hn' h
  simp only [coe_Ioc, Set.mem_Ioc] at hn hn'
  have hp := parity_of_parityset (n := n) (n' := n') (m := m) h
  have hdvd := two_dvd_pow_dvd n n' m hp
  have hK : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  rw [hK] at hn hn'
  have hlt : |(n : ℤ) - n'| < 2 ^ m := by
    have h1 : ((2 ^ m : ℕ) : ℤ) = (2 : ℤ) ^ m := by push_cast; ring
    rw [abs_lt, ← h1]
    constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  omega

/-! ### The count -/

/-- the admissible odd-step counts. -/
def admissible (m : ℕ) : Finset ℕ :=
  (range (m + 1)).filter (fun e => 2 ^ (m * (e + 1)) ≤ (3 * 2 ^ m + 1) ^ e)

/-- **Counting corollary, combinatorial core.**
    #{n ∈ (2^m, 2^(m+1)] : the first m iterates stay ≥ n} ≤ Σ_{e admissible} C(m, e). -/
theorem count_le (m : ℕ) :
    ((Ioc (2 ^ m) (2 ^ (m + 1))).filter (fun n => stays m n)).card
      ≤ ∑ e ∈ admissible m, m.choose e := by
  set S := (Ioc (2 ^ m) (2 ^ (m + 1))).filter (fun n => stays m n) with hS
  -- injectivity on S (a subset of the interval)
  have hinj : Set.InjOn (fun n => parityset n m) (S : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a ∈ (Ioc (2 ^ m) (2 ^ (m + 1)) : Finset ℕ) := (mem_filter.mp ha).1
    have hb' : b ∈ (Ioc (2 ^ m) (2 ^ (m + 1)) : Finset ℕ) := (mem_filter.mp hb).1
    exact parityset_injective m (mem_coe.mpr ha') (mem_coe.mpr hb') hab
  rw [← card_image_of_injOn hinj]
  -- the image lies in the union over admissible e of the e-subsets of range m
  have hsub : S.image (fun n => parityset n m) ⊆
      (admissible m).biUnion (fun e => powersetCard e (range m)) := by
    intro s hs
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hs
    have hn' := mem_filter.mp hn
    have hI := mem_Ioc.mp hn'.1
    rw [mem_biUnion]
    refine ⟨odds n m, ?_, ?_⟩
    · unfold admissible
      rw [mem_filter, mem_range]
      constructor
      · have : odds n m ≤ m := by
          rw [← card_parityset]
          exact le_trans (card_le_card (filter_subset _ _)) (by simp)
        omega
      · exact growth_ineq m n hI.1 hn'.2
    · rw [mem_powersetCard]
      exact ⟨filter_subset _ _, card_parityset n m⟩
  calc (S.image (fun n => parityset n m)).card
      ≤ ((admissible m).biUnion (fun e => powersetCard e (range m))).card := card_le_card hsub
    _ ≤ ∑ e ∈ admissible m, (powersetCard e (range m)).card := card_biUnion_le
    _ = ∑ e ∈ admissible m, m.choose e := by
        apply sum_congr rfl; intro e _; rw [card_powersetCard, card_range]

end CollatzCount
