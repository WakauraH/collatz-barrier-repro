/-
Counting.lean — 計数定理 (Theorem A) の機械検証 (コア Lean 4 のみ、mathlib 不使用)。
Barrier.lean / Collapse.lean / Rotation.lean の姉妹ファイル。

証明書系を抽象化する: 添字型 I、各 i の dyadic 深さ dep i と原子 atom i、
被覆述語 covered i n について
  hsub   : covered i n → n % 2^{dep i} = atom i     (原子への包含; 奇数法細分を吸収)
  hvalid : covered i n → iter (dep i) n < n          (自深度での降下主張; 例外は covered の外)
  hcov   : ∀ n ≥ N₀, ∃ i, covered i n               (有限個の直接検証を吸収した被覆)
このとき mod 2^K の上昇類全体から {i | K < dep i} への**単射**が存在する
(counting_lower_bound) — これが「任意の正しい系は深さ > K の証明書を上昇類の
個数 c(K) 以上含む」の構成的な形である。系として、全 K で深さ > K の証明書が
存在し (no_finite_system)、有限系は存在しない。

鍵補題は odds_mod: 最初の j パリティは n mod 2^j のみに依存する (Terras 対応の
使用部分)。定義 T / iter / odds / beta は Collapse.lean と同一 (自己完結のため再掲)。

検証: ~/.elan/bin/lean Counting.lean  (エラーなし・公理は標準のみ)
-/

def T (n : Nat) : Nat := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

def iter : Nat → Nat → Nat
  | 0, n => n
  | j + 1, n => iter j (T n)

def odds : Nat → Nat → Nat
  | 0, _ => 0
  | j + 1, n => n % 2 + odds j (T n)

def beta : Nat → Nat → Nat
  | 0, _ => 0
  | j + 1, n =>
      if n % 2 = 0 then 2 * beta j (T n)
      else 3 ^ odds j (T n) + 2 * beta j (T n)

theorem two_mul_T_even {n : Nat} (h : n % 2 = 0) : 2 * T n = n := by
  simp [T, h]; omega

theorem two_mul_T_odd {n : Nat} (h : n % 2 = 1) : 2 * T n = 3 * n + 1 := by
  simp [T, h]; omega

/-- アフィン恒等式 (Collapse.lean と同一)。 -/
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

/-- 崩壊補題 (a) (Collapse.lean と同一): 上昇接頭辞では全 n ≥ 1 で非降下。 -/
theorem climbing_no_descent (j n : Nat) (hn : 1 ≤ n)
    (h : 2 ^ j < 3 ^ odds j n) : n < iter j n := by
  have ha := affine j n
  have hm : (2 ^ j + 1) * n ≤ 3 ^ odds j n * n :=
    Nat.mul_le_mul_right n (by omega)
  have hexp : (2 ^ j + 1) * n = 2 ^ j * n + n := by rw [Nat.add_mul]; omega
  have key : 2 ^ j * n < 2 ^ j * iter j n := by omega
  exact Nat.lt_of_mul_lt_mul_left key

/-- 補助: 2^j の倍数を足しても mod 2^j は不変。 -/
theorem mod_add_pow_mul (x c j : Nat) : (2 ^ j * c + x) % 2 ^ j = x % 2 ^ j := by
  rw [Nat.add_comm, Nat.mul_comm]
  exact Nat.add_mul_mod_self_right x c (2 ^ j)

/-- T の 1 ステップは剰余を 1 レベル落として保つ: n ≡ n' (mod 2^{j+1}) なら
    パリティが一致し T n ≡ T n' (mod 2^j)。 -/
theorem T_mod {j n n' : Nat} (h : n % 2 ^ (j + 1) = n' % 2 ^ (j + 1)) :
    n % 2 = n' % 2 ∧ T n % 2 ^ j = T n' % 2 ^ j := by
  have hp : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
  have hda := Nat.div_add_mod n (2 ^ (j + 1))
  have hdb := Nat.div_add_mod n' (2 ^ (j + 1))
  have hna : n = 2 * (2 ^ j * (n / 2 ^ (j + 1))) + n % 2 ^ (j + 1) := by
    rw [← Nat.mul_assoc, ← hp]; omega
  have hnb : n' = 2 * (2 ^ j * (n' / 2 ^ (j + 1))) + n % 2 ^ (j + 1) := by
    rw [← Nat.mul_assoc, ← hp]; omega
  refine ⟨by omega, ?_⟩
  by_cases he : (n % 2 ^ (j + 1)) % 2 = 0
  · -- 偶ステップ
    have hev : n % 2 = 0 := by omega
    have hev' : n' % 2 = 0 := by omega
    have h1 : T n = 2 ^ j * (n / 2 ^ (j + 1)) + n % 2 ^ (j + 1) / 2 := by
      simp only [T]; rw [if_pos hev]; omega
    have h1' : T n' = 2 ^ j * (n' / 2 ^ (j + 1)) + n % 2 ^ (j + 1) / 2 := by
      simp only [T]; rw [if_pos hev']; omega
    rw [h1, h1', mod_add_pow_mul, mod_add_pow_mul]
  · -- 奇ステップ
    have hod : ¬ n % 2 = 0 := by omega
    have hod' : ¬ n' % 2 = 0 := by omega
    have hq : 2 ^ j * (3 * (n / 2 ^ (j + 1))) = 3 * (2 ^ j * (n / 2 ^ (j + 1))) :=
      Nat.mul_left_comm (2 ^ j) 3 (n / 2 ^ (j + 1))
    have hq' : 2 ^ j * (3 * (n' / 2 ^ (j + 1))) = 3 * (2 ^ j * (n' / 2 ^ (j + 1))) :=
      Nat.mul_left_comm (2 ^ j) 3 (n' / 2 ^ (j + 1))
    have h1 : T n = 2 ^ j * (3 * (n / 2 ^ (j + 1))) + (3 * (n % 2 ^ (j + 1)) + 1) / 2 := by
      simp only [T]; rw [if_neg hod]; omega
    have h1' : T n' = 2 ^ j * (3 * (n' / 2 ^ (j + 1))) + (3 * (n % 2 ^ (j + 1)) + 1) / 2 := by
      simp only [T]; rw [if_neg hod']; omega
    rw [h1, h1', mod_add_pow_mul, mod_add_pow_mul]

/-- 鍵補題: 最初の j パリティは n mod 2^j のみに依存する。 -/
theorem odds_mod : ∀ (j n n' : Nat), n % 2 ^ j = n' % 2 ^ j →
    odds j n = odds j n' := by
  intro j
  induction j with
  | zero => intro n n' _; simp [odds]
  | succ j ih =>
    intro n n' h
    obtain ⟨hp, hT⟩ := T_mod h
    simp only [odds]
    rw [hp, ih (T n) (T n') hT]

/-- 上昇類 (mod 2^K の剰余 x の全接頭辞が上昇)。 -/
def Climbing (K x : Nat) : Prop :=
  ∀ j, 1 ≤ j → j ≤ K → 2 ^ j < 3 ^ odds j x

/-- 計数定理 (Theorem A の核): 任意の正しい証明書系に対し、mod 2^K の上昇類
    全体から深さ > K の証明書への単射が存在する。 -/
theorem counting_lower_bound
    (I : Type) (dep : I → Nat) (atom : I → Nat)
    (covered : I → Nat → Prop)
    (hsub : ∀ i n, covered i n → n % 2 ^ dep i = atom i)
    (hvalid : ∀ i n, covered i n → iter (dep i) n < n)
    (N₀ : Nat) (hcov : ∀ n, N₀ ≤ n → ∃ i, covered i n)
    (K : Nat) :
    ∃ φ : {x : Nat // x < 2 ^ K ∧ Climbing K x} → I,
      (∀ x, K < dep (φ x)) ∧ (∀ x y, φ x = φ y → x = y) := by
  -- 各上昇剰余 x の証人: n_x = x + 2^K (N₀ + 1) (≥ N₀ かつ ≡ x mod 2^K)
  have hwit : ∀ x : {x : Nat // x < 2 ^ K ∧ Climbing K x},
      N₀ ≤ x.val + 2 ^ K * (N₀ + 1) ∧
      (x.val + 2 ^ K * (N₀ + 1)) % 2 ^ K = x.val := by
    intro x
    have hp : 0 < 2 ^ K := Nat.pow_pos (by decide)
    constructor
    · have : N₀ + 1 ≤ 2 ^ K * (N₀ + 1) := Nat.le_mul_of_pos_left _ hp
      omega
    · rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt x.property.1
  -- 深さ強制: 証人を被覆する証明書は深さ > K (さもなくば上昇接頭辞での降下)
  have hdeep : ∀ (x : {x : Nat // x < 2 ^ K ∧ Climbing K x}) (i : I),
      covered i (x.val + 2 ^ K * (N₀ + 1)) → K < dep i := by
    intro x i hc
    by_cases hdep' : dep i ≤ K
    · exfalso
      have hd := hvalid i _ hc
      by_cases h0 : dep i = 0
      · rw [h0] at hd; simp [iter] at hd
      · have hdvd : 2 ^ dep i ∣ 2 ^ K := Nat.pow_dvd_pow 2 hdep'
        have hmm := Nat.mod_mod_of_dvd (x.val + 2 ^ K * (N₀ + 1)) hdvd
        have hmod : (x.val + 2 ^ K * (N₀ + 1)) % 2 ^ dep i = x.val % 2 ^ dep i := by
          rw [(hwit x).2] at hmm; omega
        have ho := odds_mod (dep i) _ x.val hmod
        have hcl : 2 ^ dep i < 3 ^ odds (dep i) x.val :=
          x.property.2 (dep i) (by omega) hdep'
        have hn1 : 1 ≤ x.val + 2 ^ K * (N₀ + 1) := by
          have : 0 < 2 ^ K := Nat.pow_pos (by decide)
          omega
        have := climbing_no_descent (dep i) _ hn1 (by rw [ho]; exact hcl)
        omega
    · omega
  refine ⟨fun x => (hcov (x.val + 2 ^ K * (N₀ + 1)) (hwit x).1).choose,
    fun x => hdeep x _ (hcov (x.val + 2 ^ K * (N₀ + 1)) (hwit x).1).choose_spec,
    ?_⟩
  -- 単射性: 同じ証明書の原子は mod 2^K で一つの剰余に落ちる
  intro x y hxy
  have hcx := (hcov (x.val + 2 ^ K * (N₀ + 1)) (hwit x).1).choose_spec
  have hcy := (hcov (y.val + 2 ^ K * (N₀ + 1)) (hwit y).1).choose_spec
  have hxy' : (hcov (x.val + 2 ^ K * (N₀ + 1)) (hwit x).1).choose =
      (hcov (y.val + 2 ^ K * (N₀ + 1)) (hwit y).1).choose := hxy
  rw [← hxy'] at hcy
  have hax := hsub _ _ hcx
  have hay := hsub _ _ hcy
  have hdep := hdeep x _ hcx
  have hdvd : 2 ^ K ∣ 2 ^ dep ((hcov (x.val + 2 ^ K * (N₀ + 1)) (hwit x).1).choose) :=
    Nat.pow_dvd_pow 2 (by omega)
  have hx' := Nat.mod_mod_of_dvd (x.val + 2 ^ K * (N₀ + 1)) hdvd
  have hy' := Nat.mod_mod_of_dvd (y.val + 2 ^ K * (N₀ + 1)) hdvd
  have hvx := (hwit x).2
  have hvy := (hwit y).2
  have : x.val = y.val := by
    rw [hax] at hx'
    rw [hay] at hy'
    omega
  exact Subtype.ext this

/-- 全1塔の T ステップ: T(2^{m+1} t − 1) = 2^m (3t) − 1。 -/
theorem Tstep (m t : Nat) (ht : 1 ≤ t) :
    T (2 ^ (m + 1) * t - 1) = 2 ^ m * (3 * t) - 1 := by
  have hX : 1 ≤ 2 ^ m * t := Nat.mul_pos (Nat.pow_pos (by decide)) ht
  have hp : 2 ^ (m + 1) * t = 2 * (2 ^ m * t) := by
    rw [Nat.pow_succ]
    simp [Nat.mul_comm, Nat.mul_left_comm]
  have h3 : 2 ^ m * (3 * t) = 3 * (2 ^ m * t) := Nat.mul_left_comm (2 ^ m) 3 t
  have hodd : ¬ (2 ^ (m + 1) * t - 1) % 2 = 0 := by omega
  simp only [T]
  rw [if_neg hodd]
  omega

/-- 全1類の接頭辞は全て奇: odds j (2^m t − 1) = j (j ≤ m)。 -/
theorem allones : ∀ (j m t : Nat), 1 ≤ t → j ≤ m →
    odds j (2 ^ m * t - 1) = j := by
  intro j
  induction j with
  | zero => intro m t _ _; simp [odds]
  | succ j ih =>
    intro m t ht hj
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hX : 1 ≤ 2 ^ m' * t := Nat.mul_pos (Nat.pow_pos (by decide)) ht
    have hp : 2 ^ (m' + 1) * t = 2 * (2 ^ m' * t) := by
      rw [Nat.pow_succ]
      simp [Nat.mul_comm, Nat.mul_left_comm]
    have hodd : (2 ^ (m' + 1) * t - 1) % 2 = 1 := by omega
    simp only [odds, hodd, Tstep m' t ht]
    rw [ih m' (3 * t) (by omega) (by omega)]
    omega

theorem two_pow_lt_three_pow : ∀ j, 1 ≤ j → 2 ^ j < 3 ^ j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro _
    by_cases hj : j = 0
    · subst hj; decide
    · have h := ih (by omega)
      have e2 : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ ..
      have e3 : 3 ^ (j + 1) = 3 ^ j * 3 := Nat.pow_succ ..
      omega

/-- 系: 全ての K で深さ > K の証明書が存在する。ゆえに有限系は存在しない。 -/
theorem no_finite_system
    (I : Type) (dep : I → Nat) (atom : I → Nat)
    (covered : I → Nat → Prop)
    (hsub : ∀ i n, covered i n → n % 2 ^ dep i = atom i)
    (hvalid : ∀ i n, covered i n → iter (dep i) n < n)
    (N₀ : Nat) (hcov : ∀ n, N₀ ≤ n → ∃ i, covered i n) :
    ∀ K, ∃ i : I, K < dep i := by
  intro K
  obtain ⟨φ, hφ, _⟩ :=
    counting_lower_bound I dep atom covered hsub hvalid N₀ hcov K
  have hp : 0 < 2 ^ K := Nat.pow_pos (by decide)
  have hx : (2 ^ K - 1 < 2 ^ K) ∧ Climbing K (2 ^ K - 1) := by
    constructor
    · omega
    · intro j h1 hK
      have ho : odds j (2 ^ K * 1 - 1) = j := allones j K 1 (by omega) hK
      rw [Nat.mul_one] at ho
      rw [ho]
      exact two_pow_lt_three_pow j h1
  exact ⟨φ ⟨2 ^ K - 1, hx⟩, hφ ⟨2 ^ K - 1, hx⟩⟩

#print axioms odds_mod
#print axioms counting_lower_bound
#print axioms no_finite_system
