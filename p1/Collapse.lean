/-
Collapse.lean — 適応崩壊補題と持続補題の機械検証 (コア Lean 4 のみ、mathlib 不使用)。
Barrier.lean (climb 補題) の姉妹ファイル。P1 の Lemma "adaptive collapse" と
Lemma "persistence of climbing" の算術核を検証する。

T(n) = n/2 (偶) / (3n+1)/2 (奇) の j 回反復 iter j n について
  affine            : 2^j · iter j n = 3^{odds j n} · n + beta j n   (アフィン恒等式)
  beta_bound        : beta j n + 2^j ≤ 3^j                            (剰余項上界)
  climbing_no_descent : 2^j < 3^{odds j n} → n < iter j n  (全 n ≥ 1、サイズ条件なし)
  descent_forced    : 3^{odds j n} < 2^j → 3^j < n → iter j n < n     (降下の強制)
  climb_extend      : 2^k < 3^e → 2^{k+1} < 3^{e+1}                   (持続補題)

climbing_no_descent + descent_forced が「可変停止時刻は n > 3^j で第一降下時刻に
崩壊する」の核であり、climb_extend が「上昇類は全ての地平線で上昇部分類を持つ」
の核である (Theorem A′)。

検証: ~/.elan/bin/lean Collapse.lean  (エラーなし・公理は [propext, Quot.sound] のみ)
-/

/-- 圧縮 Collatz 写像 (自然数除算)。 -/
def T (n : Nat) : Nat := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- j 回反復。 -/
def iter : Nat → Nat → Nat
  | 0, n => n
  | j + 1, n => iter j (T n)

/-- 最初の j ステップ中の奇数回数 e_j。 -/
def odds : Nat → Nat → Nat
  | 0, _ => 0
  | j + 1, n => n % 2 + odds j (T n)

/-- アフィン剰余項 β_j。 -/
def beta : Nat → Nat → Nat
  | 0, _ => 0
  | j + 1, n =>
      if n % 2 = 0 then 2 * beta j (T n)
      else 3 ^ odds j (T n) + 2 * beta j (T n)

theorem two_mul_T_even {n : Nat} (h : n % 2 = 0) : 2 * T n = n := by
  simp [T, h]; omega

theorem two_mul_T_odd {n : Nat} (h : n % 2 = 1) : 2 * T n = 3 * n + 1 := by
  simp [T, h]; omega

/-- アフィン恒等式: 2^j · T^j(n) = 3^{e_j} · n + β_j。 -/
theorem affine : ∀ (j n : Nat), 2 ^ j * iter j n = 3 ^ odds j n * n + beta j n := by
  intro j
  induction j with
  | zero => intro n; simp [iter, odds, beta]
  | succ j ih =>
    intro n
    have ihT := ih (T n)
    have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
    have hsplit : n % 2 = 0 ∨ n % 2 = 1 := by omega
    cases hsplit with
    | inl h =>
      have h2T := two_mul_T_even h
      have e2 : odds (j + 1) n = odds j (T n) := by simp [odds, h]
      have e3 : beta (j + 1) n = 2 * beta j (T n) := by simp [beta, h]
      show 2 ^ (j + 1) * iter j (T n) = 3 ^ odds (j + 1) n * n + beta (j + 1) n
      rw [e2, e3, hpow, Nat.mul_assoc, ihT]
      -- 2 * (E * T n + B) = E * n + 2B, using 2 * T n = n
      calc 2 * (3 ^ odds j (T n) * T n + beta j (T n))
          = 3 ^ odds j (T n) * (2 * T n) + 2 * beta j (T n) := by
            rw [Nat.mul_add, Nat.mul_left_comm]
        _ = 3 ^ odds j (T n) * n + 2 * beta j (T n) := by rw [h2T]
    | inr h =>
      have h2T := two_mul_T_odd h
      have e2 : odds (j + 1) n = 1 + odds j (T n) := by simp [odds, h]
      have e3 : beta (j + 1) n = 3 ^ odds j (T n) + 2 * beta j (T n) := by
        simp [beta, h]
      show 2 ^ (j + 1) * iter j (T n) = 3 ^ odds (j + 1) n * n + beta (j + 1) n
      rw [e2, e3, hpow, Nat.mul_assoc, ihT]
      have hpow3 : 3 ^ (1 + odds j (T n)) = 3 * 3 ^ odds j (T n) := by
        rw [Nat.add_comm, Nat.pow_succ]; omega
      calc 2 * (3 ^ odds j (T n) * T n + beta j (T n))
          = 3 ^ odds j (T n) * (2 * T n) + 2 * beta j (T n) := by
            rw [Nat.mul_add, Nat.mul_left_comm]
        _ = 3 ^ odds j (T n) * (3 * n + 1) + 2 * beta j (T n) := by rw [h2T]
        _ = 3 * 3 ^ odds j (T n) * n + (3 ^ odds j (T n) + 2 * beta j (T n)) := by
            rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
            rw [← Nat.mul_assoc]
            omega
        _ = 3 ^ (1 + odds j (T n)) * n + (3 ^ odds j (T n) + 2 * beta j (T n)) := by
            rw [hpow3]

theorem odds_le : ∀ (j n : Nat), odds j n ≤ j := by
  intro j
  induction j with
  | zero => intro n; simp [odds]
  | succ j ih =>
    intro n
    have := ih (T n)
    have : n % 2 ≤ 1 := by omega
    simp [odds]; omega

/-- 剰余項の上界: β_j + 2^j ≤ 3^j (ゆえに β_j < 3^j)。 -/
theorem beta_bound : ∀ (j n : Nat), beta j n + 2 ^ j ≤ 3 ^ j := by
  intro j
  induction j with
  | zero => intro n; simp [beta]
  | succ j ih =>
    intro n
    have ihT := ih (T n)
    have hp2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
    have hp3 : 3 ^ (j + 1) = 3 * 3 ^ j := by rw [Nat.pow_succ]; omega
    have hE : 3 ^ odds j (T n) ≤ 3 ^ j :=
      Nat.pow_le_pow_right (by decide) (odds_le j (T n))
    have hsplit : n % 2 = 0 ∨ n % 2 = 1 := by omega
    cases hsplit with
    | inl h => simp [beta, h]; omega
    | inr h => simp [beta, h]; omega

/-- 崩壊補題 (a): 上昇接頭辞 (3^{e_j} > 2^j) では、サイズ条件なしに全ての
    n ≥ 1 で T^j(n) > n。 -/
theorem climbing_no_descent (j n : Nat) (hn : 1 ≤ n)
    (h : 2 ^ j < 3 ^ odds j n) : n < iter j n := by
  have ha := affine j n
  have hm : (2 ^ j + 1) * n ≤ 3 ^ odds j n * n :=
    Nat.mul_le_mul_right n (by omega)
  have hexp : (2 ^ j + 1) * n = 2 ^ j * n + n := by rw [Nat.add_mul]; omega
  have key : 2 ^ j * n < 2 ^ j * iter j n := by omega
  exact Nat.lt_of_mul_lt_mul_left key

/-- 崩壊補題 (b): 非上昇接頭辞 (3^{e_j} < 2^j) では、n > 3^j なら T^j(n) < n
    (降下の強制)。可変停止時刻は n > 3^j で第一降下時刻に崩壊する。 -/
theorem descent_forced (j n : Nat) (h1 : 3 ^ odds j n < 2 ^ j)
    (h2 : 3 ^ j < n) : iter j n < n := by
  have ha := affine j n
  have hb := beta_bound j n
  have hp2 : 0 < 2 ^ j := Nat.pow_pos (by decide)
  have hp3 : 0 < 3 ^ odds j n := Nat.pow_pos (by decide)
  have hp3j : 0 < 3 ^ j := Nat.pow_pos (by decide)
  have hm : (3 ^ odds j n + 1) * n ≤ 2 ^ j * n :=
    Nat.mul_le_mul_right n (by omega)
  have hexp : (3 ^ odds j n + 1) * n = 3 ^ odds j n * n + n := by
    rw [Nat.add_mul]; omega
  have key : 2 ^ j * iter j n < 2 ^ j * n := by omega
  exact Nat.lt_of_mul_lt_mul_left key

/-- 持続補題: 上昇条件 3^e > 2^k は 1 を付加しても保たれる。ゆえに上昇類は
    どの深い地平線でも上昇部分類を含み、c(k+1) ≥ c(k)。 -/
theorem climb_extend (k e : Nat) (h : 2 ^ k < 3 ^ e) :
    2 ^ (k + 1) < 3 ^ (e + 1) := by
  rw [Nat.pow_succ, Nat.pow_succ]; omega

#print axioms affine
#print axioms beta_bound
#print axioms climbing_no_descent
#print axioms descent_forced
#print axioms climb_extend
