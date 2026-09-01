/-
Barrier.lean — 障壁補題の機械検証 (コア Lean 4 のみ、mathlib 不使用)。

主張 (climb): 1 ≤ t, 1 ≤ i のとき、f(n) = (3n+1)/2 の j 回反復は
    orbit j (2^(j+i) t - 1) + 1 = 3^j 2^i t
を満たす。系として
  - climb_mod: 各反復値は奇数 (よって f-軌道は加速写像 U の軌道と一致、a_j = 1)
  - climb_ge : j ステップ後も初期値以上 (降下しない)
  - barrier  : n = 2^m t - 1 は最初の m-1 ステップで初期値未満に降下しない
これは「深さ K の一様降下証明書は類 -1 mod 2^m (m > K) を処理できない」
という有限被覆障壁の核である。

検証: ~/.elan/bin/lean Barrier.lean  (エラーなし・公理は標準 [propext, Quot.sound] のみ)
-/

/-- 圧縮 Collatz 奇数ステップ f(n) = (3n+1)/2 (自然数除算)。 -/
def f (n : Nat) : Nat := (3 * n + 1) / 2

/-- j 回反復。 -/
def orbit : Nat → Nat → Nat
  | 0, n => n
  | j + 1, n => orbit j (f n)

theorem climb : ∀ (j i t : Nat), 1 ≤ t → 1 ≤ i →
    orbit j (2 ^ (j + i) * t - 1) + 1 = 3 ^ j * 2 ^ i * t := by
  intro j
  induction j with
  | zero =>
    intro i t ht hi
    have h1 : 0 < 2 ^ i * t := Nat.mul_pos (Nat.pow_pos (by decide)) ht
    show 2 ^ (0 + i) * t - 1 + 1 = 3 ^ 0 * 2 ^ i * t
    rw [Nat.zero_add, Nat.pow_zero, Nat.one_mul]
    omega
  | succ j ih =>
    intro i t ht hi
    show orbit j (f (2 ^ (j + 1 + i) * t - 1)) + 1 = 3 ^ (j + 1) * 2 ^ i * t
    have hX : 0 < 2 ^ (j + i) * t :=
      Nat.mul_pos (Nat.pow_pos (by decide)) ht
    have harg : 2 ^ (j + 1 + i) * t = 2 * (2 ^ (j + i) * t) := by
      have e1 : j + 1 + i = (j + i) + 1 := by omega
      rw [e1, Nat.pow_succ]
      simp [Nat.mul_comm, Nat.mul_left_comm]
    have hout : 2 ^ (j + i) * (3 * t) = 3 * (2 ^ (j + i) * t) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have h1 : f (2 ^ (j + 1 + i) * t - 1) = 2 ^ (j + i) * (3 * t) - 1 := by
      unfold f
      rw [harg, hout]
      omega
    rw [h1]
    have h4 := ih i (3 * t) (by omega) hi
    rw [h4, Nat.pow_succ]
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- 各反復値は奇数: よって f-軌道は U-軌道と一致し、各ステップの 2 進付値 a_j = 1。 -/
theorem climb_mod (j i t : Nat) (ht : 1 ≤ t) (hi : 1 ≤ i) :
    orbit j (2 ^ (j + i) * t - 1) % 2 = 1 := by
  have h := climb j i t ht hi
  obtain ⟨i', hi'⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hc : 3 ^ j * 2 ^ i * t = 2 * (3 ^ j * 2 ^ i' * t) := by
    rw [hi', Nat.pow_succ]
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  rw [hc] at h
  omega

/-- 非降下: j ステップ後も初期値以上。 -/
theorem climb_ge (j i t : Nat) (ht : 1 ≤ t) (hi : 1 ≤ i) :
    2 ^ (j + i) * t - 1 ≤ orbit j (2 ^ (j + i) * t - 1) := by
  have h := climb j i t ht hi
  have h2 : 2 ^ j ≤ 3 ^ j := Nat.pow_le_pow_left (by decide) j
  have h5 : 2 ^ (j + i) * t = 2 ^ j * 2 ^ i * t := by rw [Nat.pow_add]
  have h4 : 2 ^ j * 2 ^ i * t ≤ 3 ^ j * 2 ^ i * t :=
    Nat.mul_le_mul_right t (Nat.mul_le_mul_right (2 ^ i) h2)
  omega

/-- 障壁定理: n = 2^m t - 1 (t ≥ 1) は最初の m-1 ステップで初期値未満に降下しない。 -/
theorem barrier (m t : Nat) (hm : 1 ≤ m) (ht : 1 ≤ t) :
    ∀ j, j ≤ m - 1 → 2 ^ m * t - 1 ≤ orbit j (2 ^ m * t - 1) := by
  intro j hj
  have hjm : j + (m - j) = m := by omega
  have hi : 1 ≤ m - j := by omega
  have h := climb_ge j (m - j) t ht hi
  rw [hjm] at h
  exact h

#print axioms climb
#print axioms climb_mod
#print axioms climb_ge
#print axioms barrier
