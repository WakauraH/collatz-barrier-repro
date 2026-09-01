/-
Rotation.lean — 回転補題の算術核の機械検証 (コア Lean 4 のみ、mathlib 不使用)。
Barrier.lean / Collapse.lean の姉妹ファイル。P1 の rotation lemma (Theorem B の
下界 c(k) ≥ C(k,⌈θk⌉)/k の核) を検証する。

定式化: 語の接頭辞カウント関数 e : Nat → Nat (e 0 = 0) に対し、実数の重み
S_j = e_j − θj の比較を交差積で整数化する: S_a ≤ S_b ⟺ 3^{e a}·2^b ≤ 3^{e b}·2^a。
総和条件 2^k < 3^{e k} (= S_k > 0) の下で、回転点 r < k が存在して
  第1群 (i ∈ (r, k]):   3^{e r}·2^i < 3^{e i}·2^r      (= S_r < S_i)
  第2群 (t ∈ [1, r]):   2^{k+t}·3^{e r} < 3^{e k + e t}·2^r
これは回転語 (b_{r+1..k} b_{1..r}) の全接頭辞上昇条件
2^i < 3^{e'_i} の交差積形そのものである (変数変換は一行)。

論文証明は θ の無理性 (同値の非存在) を使うが、本形式化は「最後の最小点」を
取ることで無理性を完全に回避する — 離散版の方が仮定が少ない。

検証: ~/.elan/bin/lean Rotation.lean  (エラーなし・公理は標準のみ)
-/

/-- 正数倍は狭義単調。 -/
theorem mul_lt_mul_of_pos_left' {a b k : Nat} (h : a < b) (hk : 0 < k) :
    k * a < k * b := by
  have h1 : k * (a + 1) ≤ k * b := Nat.mul_le_mul_left k (by omega)
  have h2 : k * (a + 1) = k * a + k := Nat.mul_succ k a
  omega

/-- 交差積比較の推移律: S_a ≤ S_b ≤ S_c ⇒ S_a ≤ S_c。 -/
theorem sle_trans (e : Nat → Nat) {a b c : Nat}
    (h1 : 3 ^ e a * 2 ^ b ≤ 3 ^ e b * 2 ^ a)
    (h2 : 3 ^ e b * 2 ^ c ≤ 3 ^ e c * 2 ^ b) :
    3 ^ e a * 2 ^ c ≤ 3 ^ e c * 2 ^ a := by
  have h1' : (3 ^ e a * 2 ^ b) * 2 ^ c ≤ (3 ^ e b * 2 ^ a) * 2 ^ c :=
    Nat.mul_le_mul_right _ h1
  have h2' : (3 ^ e b * 2 ^ c) * 2 ^ a ≤ (3 ^ e c * 2 ^ b) * 2 ^ a :=
    Nat.mul_le_mul_right _ h2
  have hchain : 2 ^ b * (3 ^ e a * 2 ^ c) ≤ 2 ^ b * (3 ^ e c * 2 ^ a) := by
    have e1 : 2 ^ b * (3 ^ e a * 2 ^ c) = (3 ^ e a * 2 ^ b) * 2 ^ c := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    have e2 : (3 ^ e b * 2 ^ a) * 2 ^ c = (3 ^ e b * 2 ^ c) * 2 ^ a := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    have e3 : (3 ^ e c * 2 ^ b) * 2 ^ a = 2 ^ b * (3 ^ e c * 2 ^ a) := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    calc 2 ^ b * (3 ^ e a * 2 ^ c) = (3 ^ e a * 2 ^ b) * 2 ^ c := e1
      _ ≤ (3 ^ e b * 2 ^ a) * 2 ^ c := h1'
      _ = (3 ^ e b * 2 ^ c) * 2 ^ a := e2
      _ ≤ (3 ^ e c * 2 ^ b) * 2 ^ a := h2'
      _ = 2 ^ b * (3 ^ e c * 2 ^ a) := e3
  exact Nat.le_of_mul_le_mul_left hchain (Nat.pow_pos (by decide))

/-- 交差積比較の混合推移律: S_a ≤ S_b < S_c ⇒ S_a < S_c。 -/
theorem sle_lt_trans (e : Nat → Nat) {a b c : Nat}
    (h1 : 3 ^ e a * 2 ^ b ≤ 3 ^ e b * 2 ^ a)
    (h2 : 3 ^ e b * 2 ^ c < 3 ^ e c * 2 ^ b) :
    3 ^ e a * 2 ^ c < 3 ^ e c * 2 ^ a := by
  have h1' : (3 ^ e a * 2 ^ b) * 2 ^ c ≤ (3 ^ e b * 2 ^ a) * 2 ^ c :=
    Nat.mul_le_mul_right _ h1
  have h2' : 2 ^ a * (3 ^ e b * 2 ^ c) < 2 ^ a * (3 ^ e c * 2 ^ b) :=
    mul_lt_mul_of_pos_left' h2 (Nat.pow_pos (by decide))
  have hchain : 2 ^ b * (3 ^ e a * 2 ^ c) < 2 ^ b * (3 ^ e c * 2 ^ a) := by
    have e1 : 2 ^ b * (3 ^ e a * 2 ^ c) = (3 ^ e a * 2 ^ b) * 2 ^ c := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    have e2 : (3 ^ e b * 2 ^ a) * 2 ^ c = 2 ^ a * (3 ^ e b * 2 ^ c) := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    have e3 : 2 ^ a * (3 ^ e c * 2 ^ b) = 2 ^ b * (3 ^ e c * 2 ^ a) := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    calc 2 ^ b * (3 ^ e a * 2 ^ c) = (3 ^ e a * 2 ^ b) * 2 ^ c := e1
      _ ≤ (3 ^ e b * 2 ^ a) * 2 ^ c := h1'
      _ = 2 ^ a * (3 ^ e b * 2 ^ c) := e2
      _ < 2 ^ a * (3 ^ e c * 2 ^ b) := h2'
      _ = 2 ^ b * (3 ^ e c * 2 ^ a) := e3
  exact Nat.lt_of_mul_lt_mul_left hchain

/-- S 値の最後の最小点 (0..m を走査、同値なら後を採る)。 -/
def am (e : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 =>
      if 3 ^ e (m + 1) * 2 ^ am e m ≤ 3 ^ e (am e m) * 2 ^ (m + 1)
      then m + 1 else am e m

theorem am_le (e : Nat → Nat) : ∀ m, am e m ≤ m := by
  intro m
  induction m with
  | zero => simp [am]
  | succ m ih =>
    by_cases hc : 3 ^ e (m + 1) * 2 ^ am e m ≤ 3 ^ e (am e m) * 2 ^ (m + 1)
    · simp [am, hc]
    · simp [am, hc]; omega

/-- 最小性: S_{am m} ≤ S_j (0 ≤ j ≤ m)。 -/
theorem am_min (e : Nat → Nat) : ∀ m j, j ≤ m →
    3 ^ e (am e m) * 2 ^ j ≤ 3 ^ e j * 2 ^ (am e m) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    have : j = 0 := by omega
    subst this; simp [am]
  | succ m ih =>
    intro j hj
    by_cases hc : 3 ^ e (m + 1) * 2 ^ am e m ≤ 3 ^ e (am e m) * 2 ^ (m + 1)
    · -- am e (m+1) = m+1、S_{m+1} ≤ S_{am m}
      simp only [am, hc, if_pos]
      by_cases hjm : j = m + 1
      · subst hjm; exact Nat.le_refl _
      · have hj' : j ≤ m := by omega
        exact sle_trans e hc (ih j hj')
    · -- am e (m+1) = am e m、S_{am m} < S_{m+1}
      simp only [am, hc, if_neg, not_false_iff]
      by_cases hjm : j = m + 1
      · subst hjm; omega
      · exact ih j (by omega)

/-- 後方狭義性: am m < j ≤ m ⇒ S_{am m} < S_j (最後の最小点ゆえ)。 -/
theorem am_strict (e : Nat → Nat) : ∀ m j, j ≤ m → am e m < j →
    3 ^ e (am e m) * 2 ^ j < 3 ^ e j * 2 ^ (am e m) := by
  intro m
  induction m with
  | zero => intro j hj hlt; omega
  | succ m ih =>
    intro j hj hlt
    by_cases hc : 3 ^ e (m + 1) * 2 ^ am e m ≤ 3 ^ e (am e m) * 2 ^ (m + 1)
    · simp only [am, hc, if_pos] at hlt ⊢
      omega
    · simp only [am, hc, if_neg, not_false_iff] at hlt ⊢
      by_cases hjm : j = m + 1
      · subst hjm; omega
      · exact ih j (by omega) hlt

/-- 回転補題 (算術核): e 0 = 0、総和条件 2^k < 3^{e k} のもとで、回転点 r < k が
    存在し、回転語の全接頭辞上昇条件が (交差積形で) 成立する。
    第1群は位置 i−r (i ∈ (r,k])、第2群は位置 (k−r)+t (t ∈ [1,r]) に対応する。 -/
theorem rotation (e : Nat → Nat) (k : Nat) (h0 : e 0 = 0)
    (hk : 2 ^ k < 3 ^ e k) :
    ∃ r, r < k ∧
      (∀ i, r < i → i ≤ k → 3 ^ e r * 2 ^ i < 3 ^ e i * 2 ^ r) ∧
      (∀ t, 1 ≤ t → t ≤ r → 2 ^ (k + t) * 3 ^ e r < 3 ^ (e k + e t) * 2 ^ r) := by
  -- k ≥ 1 (さもなくば総和条件が 1 < 1)
  have hk1 : 1 ≤ k := by
    by_cases h : k = 0
    · subst h; rw [h0] at hk; simp at hk
    · omega
  refine ⟨am e (k - 1), by have := am_le e (k - 1); omega, ?_, ?_⟩
  · -- 第1群
    intro i hri hik
    by_cases hik' : i = k
    · -- i = k: S_r ≤ S_0 < S_k
      rw [hik']
      have hA : 3 ^ e (am e (k - 1)) * 2 ^ 0 ≤ 3 ^ e 0 * 2 ^ (am e (k - 1)) :=
        am_min e (k - 1) 0 (by omega)
      have hB : 3 ^ e 0 * 2 ^ k < 3 ^ e k * 2 ^ 0 := by
        rw [h0]; simpa using hk
      exact sle_lt_trans e hA hB
    · -- i ≤ k−1: 最後の最小点の後方狭義性
      exact am_strict e (k - 1) i (by omega) hri
  · -- 第2群: S_r ≤ S_t と S_k > 0 の積
    intro t ht htr
    have hA : 3 ^ e (am e (k - 1)) * 2 ^ t ≤ 3 ^ e t * 2 ^ (am e (k - 1)) :=
      am_min e (k - 1) t (by have := am_le e (k - 1); omega)
    have step1 : (3 ^ e (am e (k - 1)) * 2 ^ t) * 2 ^ k ≤
        (3 ^ e t * 2 ^ (am e (k - 1))) * 2 ^ k :=
      Nat.mul_le_mul_right _ hA
    have step2 : (3 ^ e t * 2 ^ (am e (k - 1))) * 2 ^ k <
        (3 ^ e t * 2 ^ (am e (k - 1))) * 3 ^ e k :=
      mul_lt_mul_of_pos_left' hk
        (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)))
    -- 並べ替えて主張の形へ
    have eL : 2 ^ (k + t) * 3 ^ e (am e (k - 1)) =
        (3 ^ e (am e (k - 1)) * 2 ^ t) * 2 ^ k := by
      rw [Nat.pow_add]
      simp [Nat.mul_comm, Nat.mul_assoc]
    have eR : (3 ^ e t * 2 ^ (am e (k - 1))) * 3 ^ e k =
        3 ^ (e k + e t) * 2 ^ (am e (k - 1)) := by
      rw [Nat.pow_add]
      simp [Nat.mul_comm, Nat.mul_left_comm]
    calc 2 ^ (k + t) * 3 ^ e (am e (k - 1))
        = (3 ^ e (am e (k - 1)) * 2 ^ t) * 2 ^ k := eL
      _ ≤ (3 ^ e t * 2 ^ (am e (k - 1))) * 2 ^ k := step1
      _ < (3 ^ e t * 2 ^ (am e (k - 1))) * 3 ^ e k := step2
      _ = 3 ^ (e k + e t) * 2 ^ (am e (k - 1)) := eR

#print axioms sle_trans
#print axioms sle_lt_trans
#print axioms am_min
#print axioms am_strict
#print axioms rotation
