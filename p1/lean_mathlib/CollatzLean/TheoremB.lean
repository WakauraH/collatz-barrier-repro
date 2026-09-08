import Mathlib

/-!
TheoremB.lean — Theorem B (the sandwich for c(k)) formalized against Mathlib.

Words of length k are `List.Vector Bool k`; the prefix count is
  e(l, j) := (l.take j).count true,
and l is *climbing* iff 2^j < 3^{e(l,j)} for all 1 ≤ j ≤ k.  c k is the number of
climbing words.

Lower bound (rotation): every word with e ones, 2^k < 3^e, has a climbing rotation
(the integer rotation theorem of Rotation.lean, reproduced here in namespace `Rot`),
and the map "word ↦ its climbing rotation" is at most k-to-1.  Hence
  #{words with e ones} ≤ k · c k.
Upper bound: climbing forces e ≥ e₀ := min{e : 2^k < 3^e}, and e₀ > k/2, so
  c k ≤ Σ_{e ≥ e₀} #{words with e ones} ≤ (k+1) · #{words with e₀ ones}
using the monotone decrease of the binomial coefficients above the middle.
-/

open Finset

namespace Rot
/-! The integer rotation theorem (core proofs, identical to Rotation.lean). -/

theorem mul_lt_mul_pos_left_nat {a b k : ℕ} (h : a < b) (hk : 0 < k) : k * a < k * b := by
  have h1 : k * (a + 1) ≤ k * b := Nat.mul_le_mul_left k (by omega)
  have h2 : k * (a + 1) = k * a + k := Nat.mul_succ k a
  omega

theorem sle_trans (e : ℕ → ℕ) {a b c : ℕ}
    (h1 : 3 ^ e a * 2 ^ b ≤ 3 ^ e b * 2 ^ a)
    (h2 : 3 ^ e b * 2 ^ c ≤ 3 ^ e c * 2 ^ b) :
    3 ^ e a * 2 ^ c ≤ 3 ^ e c * 2 ^ a := by
  have h1' : (3 ^ e a * 2 ^ b) * 2 ^ c ≤ (3 ^ e b * 2 ^ a) * 2 ^ c :=
    Nat.mul_le_mul_right _ h1
  have h2' : (3 ^ e b * 2 ^ c) * 2 ^ a ≤ (3 ^ e c * 2 ^ b) * 2 ^ a :=
    Nat.mul_le_mul_right _ h2
  have hchain : 2 ^ b * (3 ^ e a * 2 ^ c) ≤ 2 ^ b * (3 ^ e c * 2 ^ a) := by
    calc 2 ^ b * (3 ^ e a * 2 ^ c) = (3 ^ e a * 2 ^ b) * 2 ^ c := by ring
      _ ≤ (3 ^ e b * 2 ^ a) * 2 ^ c := h1'
      _ = (3 ^ e b * 2 ^ c) * 2 ^ a := by ring
      _ ≤ (3 ^ e c * 2 ^ b) * 2 ^ a := h2'
      _ = 2 ^ b * (3 ^ e c * 2 ^ a) := by ring
  exact Nat.le_of_mul_le_mul_left hchain (Nat.pow_pos (by norm_num))

theorem sle_lt_trans (e : ℕ → ℕ) {a b c : ℕ}
    (h1 : 3 ^ e a * 2 ^ b ≤ 3 ^ e b * 2 ^ a)
    (h2 : 3 ^ e b * 2 ^ c < 3 ^ e c * 2 ^ b) :
    3 ^ e a * 2 ^ c < 3 ^ e c * 2 ^ a := by
  have h1' : (3 ^ e a * 2 ^ b) * 2 ^ c ≤ (3 ^ e b * 2 ^ a) * 2 ^ c :=
    Nat.mul_le_mul_right _ h1
  have h2' : 2 ^ a * (3 ^ e b * 2 ^ c) < 2 ^ a * (3 ^ e c * 2 ^ b) :=
    mul_lt_mul_pos_left_nat h2 (Nat.pow_pos (by norm_num))
  have hchain : 2 ^ b * (3 ^ e a * 2 ^ c) < 2 ^ b * (3 ^ e c * 2 ^ a) := by
    calc 2 ^ b * (3 ^ e a * 2 ^ c) = (3 ^ e a * 2 ^ b) * 2 ^ c := by ring
      _ ≤ (3 ^ e b * 2 ^ a) * 2 ^ c := h1'
      _ = 2 ^ a * (3 ^ e b * 2 ^ c) := by ring
      _ < 2 ^ a * (3 ^ e c * 2 ^ b) := h2'
      _ = 2 ^ b * (3 ^ e c * 2 ^ a) := by ring
  exact Nat.lt_of_mul_lt_mul_left hchain

def am (e : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
      if 3 ^ e (m + 1) * 2 ^ am e m ≤ 3 ^ e (am e m) * 2 ^ (m + 1)
      then m + 1 else am e m

theorem am_le (e : ℕ → ℕ) : ∀ m, am e m ≤ m := by
  intro m
  induction m with
  | zero => simp [am]
  | succ m ih =>
    by_cases hc : 3 ^ e (m + 1) * 2 ^ am e m ≤ 3 ^ e (am e m) * 2 ^ (m + 1)
    · simp [am, hc]
    · simp [am, hc]; omega

theorem am_min (e : ℕ → ℕ) : ∀ m j, j ≤ m →
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
    · simp only [am, hc, if_pos]
      by_cases hjm : j = m + 1
      · subst hjm; exact Nat.le_refl _
      · exact sle_trans e hc (ih j (by omega))
    · simp only [am, hc, if_neg, not_false_iff]
      by_cases hjm : j = m + 1
      · subst hjm; omega
      · exact ih j (by omega)

theorem am_strict (e : ℕ → ℕ) : ∀ m j, j ≤ m → am e m < j →
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

theorem rotation (e : ℕ → ℕ) (k : ℕ) (h0 : e 0 = 0) (hk : 2 ^ k < 3 ^ e k) :
    ∃ r, r < k ∧
      (∀ i, r < i → i ≤ k → 3 ^ e r * 2 ^ i < 3 ^ e i * 2 ^ r) ∧
      (∀ t, 1 ≤ t → t ≤ r → 2 ^ (k + t) * 3 ^ e r < 3 ^ (e k + e t) * 2 ^ r) := by
  have hk1 : 1 ≤ k := by
    by_cases h : k = 0
    · subst h; rw [h0] at hk; simp at hk
    · omega
  refine ⟨am e (k - 1), by have := am_le e (k - 1); omega, ?_, ?_⟩
  · intro i hri hik
    by_cases hik' : i = k
    · rw [hik']
      have hA : 3 ^ e (am e (k - 1)) * 2 ^ 0 ≤ 3 ^ e 0 * 2 ^ (am e (k - 1)) :=
        am_min e (k - 1) 0 (by omega)
      have hB : 3 ^ e 0 * 2 ^ k < 3 ^ e k * 2 ^ 0 := by
        rw [h0]; simpa using hk
      exact sle_lt_trans e hA hB
    · exact am_strict e (k - 1) i (by omega) hri
  · intro t ht htr
    have hA : 3 ^ e (am e (k - 1)) * 2 ^ t ≤ 3 ^ e t * 2 ^ (am e (k - 1)) :=
      am_min e (k - 1) t (by have := am_le e (k - 1); omega)
    have step1 : (3 ^ e (am e (k - 1)) * 2 ^ t) * 2 ^ k ≤
        (3 ^ e t * 2 ^ (am e (k - 1))) * 2 ^ k :=
      Nat.mul_le_mul_right _ hA
    have step2 : (3 ^ e t * 2 ^ (am e (k - 1))) * 2 ^ k <
        (3 ^ e t * 2 ^ (am e (k - 1))) * 3 ^ e k :=
      mul_lt_mul_pos_left_nat hk
        (Nat.mul_pos (Nat.pow_pos (by norm_num)) (Nat.pow_pos (by norm_num)))
    calc 2 ^ (k + t) * 3 ^ e (am e (k - 1))
        = (3 ^ e (am e (k - 1)) * 2 ^ t) * 2 ^ k := by ring
      _ ≤ (3 ^ e t * 2 ^ (am e (k - 1))) * 2 ^ k := step1
      _ < (3 ^ e t * 2 ^ (am e (k - 1))) * 3 ^ e k := step2
      _ = 3 ^ (e k + e t) * 2 ^ (am e (k - 1)) := by ring

end Rot

namespace CollatzB

/-- Prefix count of ones. -/
def pc (l : List Bool) (j : ℕ) : ℕ := (l.take j).count true

/-- Climbing words. -/
def Climbing (l : List Bool) : Prop :=
  ∀ j, 1 ≤ j → j ≤ l.length → 2 ^ j < 3 ^ pc l j

/-! ### Prefix counts under rotation -/

theorem pc_zero (l : List Bool) : pc l 0 = 0 := by simp [pc]

theorem pc_length (l : List Bool) : pc l l.length = l.count true := by
  simp [pc]

theorem pc_add (l : List Bool) (r i : ℕ) :
    pc l (r + i) = pc l r + (List.take i (List.drop r l)).count true := by
  simp [pc, List.take_add, List.count_append]

theorem count_split (l : List Bool) (r : ℕ) :
    l.count true = pc l r + (List.drop r l).count true := by
  unfold pc
  rw [← List.count_append, List.take_append_drop]

theorem take_rotate_small (l : List Bool) {r i : ℕ} (hr : r ≤ l.length)
    (hi : i ≤ l.length - r) :
    List.take i (l.rotate r) = List.take i (List.drop r l) := by
  rw [List.rotate_eq_drop_append_take hr, List.take_append_of_le_length]
  simpa using hi

theorem take_rotate_large (l : List Bool) {r i : ℕ} (hr : r ≤ l.length)
    (hi : l.length - r ≤ i) (hik : i ≤ l.length) :
    List.take i (l.rotate r) = List.drop r l ++ List.take (i - (l.length - r)) l := by
  obtain ⟨t, ht⟩ : ∃ t, i = (List.drop r l).length + t :=
    ⟨i - (l.length - r), by simp only [List.length_drop]; omega⟩
  have htr : t ≤ r := by simp only [List.length_drop] at ht; omega
  rw [List.rotate_eq_drop_append_take hr, ht, List.take_append, List.take_take]
  have e1 : List.take ((List.drop r l).length + t) (List.drop r l) = List.drop r l :=
    List.take_of_length_le (by omega)
  rw [e1, Nat.add_sub_cancel_left, Nat.min_eq_left htr]
  congr 2
  simp only [List.length_drop]
  omega

/-- Cancel 3^a·2^b from a cross-multiplied inequality. -/
theorem cancel_pow {a b x y : ℕ} (h : 3 ^ a * 2 ^ b * x < 3 ^ a * 2 ^ b * y) : x < y :=
  Nat.lt_of_mul_lt_mul_left h

/-- The rotation at the last minimum is climbing. -/
theorem rotate_climbing (l : List Bool) (hk : 2 ^ l.length < 3 ^ l.count true) :
    ∃ r, r < l.length ∧ Climbing (l.rotate r) := by
  obtain ⟨r, hr, hg1, hg2⟩ :=
    Rot.rotation (pc l) l.length (pc_zero l) (by rw [pc_length]; exact hk)
  refine ⟨r, hr, ?_⟩
  intro i hi1 hi
  rw [List.length_rotate] at hi
  by_cases hsmall : i ≤ l.length - r
  · -- first group: position i ↦ prefix r + i of l
    have hg := hg1 (r + i) (by omega) (by omega)
    rw [pc_add] at hg
    have key : 3 ^ pc l r * 2 ^ r * 2 ^ i < 3 ^ pc l r * 2 ^ r *
        3 ^ (List.take i (List.drop r l)).count true := by
      calc 3 ^ pc l r * 2 ^ r * 2 ^ i = 3 ^ pc l r * 2 ^ (r + i) := by ring
        _ < 3 ^ (pc l r + (List.take i (List.drop r l)).count true) * 2 ^ r := hg
        _ = 3 ^ pc l r * 2 ^ r * 3 ^ (List.take i (List.drop r l)).count true := by ring
    have := cancel_pow key
    unfold pc
    rw [take_rotate_small l (by omega) hsmall]
    exact this
  · -- second group: position i = (k - r) + t with 1 ≤ t ≤ r
    have hbig : l.length - r < i := Nat.lt_of_not_le hsmall
    obtain ⟨t, ht⟩ : ∃ t, i = (l.length - r) + t := ⟨i - (l.length - r), by omega⟩
    have hg := hg2 t (by omega) (by omega)
    rw [pc_length] at hg
    have hcs := count_split l r
    have key : 3 ^ pc l r * 2 ^ r * 2 ^ i < 3 ^ pc l r * 2 ^ r *
        3 ^ ((List.drop r l).count true + pc l t) := by
      have e1 : 2 ^ (l.length + t) * 3 ^ pc l r = 3 ^ pc l r * 2 ^ r * 2 ^ i := by
        have : l.length + t = r + i := by omega
        rw [this]; ring
      have e2 : 3 ^ (l.count true + pc l t) * 2 ^ r =
          3 ^ pc l r * 2 ^ r * 3 ^ ((List.drop r l).count true + pc l t) := by
        rw [hcs]; ring
      rw [← e1, ← e2]; exact hg
    have := cancel_pow key
    have hti : i - (l.length - r) = t := by omega
    unfold pc
    rw [take_rotate_large l (by omega) (by omega) hi, List.count_append, hti]
    exact this

/-! ### Counting -/

variable (k : ℕ)

/-- Rotation of a vector. -/
def rotV (r : ℕ) (v : List.Vector Bool k) : List.Vector Bool k :=
  ⟨v.toList.rotate r, by simp⟩

theorem rotV_rotV (r s : ℕ) (v : List.Vector Bool k) :
    rotV k s (rotV k r v) = rotV k (r + s) v := by
  apply List.Vector.eq
  simp [rotV, List.rotate_rotate]

theorem rotV_length (v : List.Vector Bool k) : rotV k k v = v := by
  apply List.Vector.eq
  show v.toList.rotate k = v.toList
  rw [List.rotate_eq_drop_append_take (by simp), List.drop_of_length_le (by simp),
    List.take_of_length_le (by simp)]
  simp

open Classical in
/-- The set of climbing words of length k and its cardinality c(k). -/
noncomputable def climbSet : Finset (List.Vector Bool k) :=
  Finset.univ.filter (fun v => Climbing v.toList)

open Classical in
noncomputable def c : ℕ := (climbSet k).card

/-- Words with exactly e ones. -/
def wordsWith (e : ℕ) : Finset (List.Vector Bool k) :=
  Finset.univ.filter (fun v => v.toList.count true = e)

open Classical in
/-- The climbing rotation of a word (identity if the word has too few ones). -/
noncomputable def climbRot (v : List.Vector Bool k) : List.Vector Bool k :=
  if h : 2 ^ k < 3 ^ v.toList.count true then
    rotV k (Classical.choose (rotate_climbing v.toList (by simpa using h))) v
  else v

open Classical in
theorem climbRot_spec (v : List.Vector Bool k) (h : 2 ^ k < 3 ^ v.toList.count true) :
    Climbing (climbRot k v).toList ∧
    ∃ r, r < k ∧ climbRot k v = rotV k r v := by
  have h' : 2 ^ v.toList.length < 3 ^ v.toList.count true := by simpa using h
  have hs := Classical.choose_spec (rotate_climbing v.toList h')
  refine ⟨?_, Classical.choose (rotate_climbing v.toList h'), ?_, ?_⟩
  · simp only [climbRot, dif_pos h]
    exact hs.2
  · simpa using hs.1
  · simp only [climbRot, dif_pos h]

open Classical in
/-- **Lower bound**: #{words with e ones} ≤ k · c(k) whenever 2^k < 3^e. -/
theorem lower_bound (e : ℕ) (he : 2 ^ k < 3 ^ e) :
    (wordsWith k e).card ≤ k * c k := by
  have hfib : ∀ w ∈ (wordsWith k e).image (climbRot k),
      ((wordsWith k e).filter (fun v => climbRot k v = w)).card ≤ k := by
    intro w hw
    -- every preimage v satisfies v = rotV (k - r) w for some r < k
    have hsub : (wordsWith k e).filter (fun v => climbRot k v = w) ⊆
        (Finset.range k).image (fun s => rotV k s w) := by
      intro v hv
      rw [Finset.mem_filter] at hv
      obtain ⟨hv1, hv2⟩ := hv
      have hcount : v.toList.count true = e := by
        simpa [wordsWith] using hv1
      obtain ⟨_, r, hr, hrot⟩ := climbRot_spec k v (by rw [hcount]; exact he)
      rw [Finset.mem_image]
      refine ⟨(k - r) % k, by simp; exact Nat.mod_lt _ (by omega), ?_⟩
      rw [← hv2, hrot, rotV_rotV]
      by_cases hr0 : r = 0
      · subst hr0; simp [rotV]
      · have : r + (k - r) % k = k := by rw [Nat.mod_eq_of_lt (by omega)]; omega
        rw [this, rotV_length]
    calc ((wordsWith k e).filter (fun v => climbRot k v = w)).card
        ≤ ((Finset.range k).image (fun s => rotV k s w)).card := Finset.card_le_card hsub
      _ ≤ (Finset.range k).card := Finset.card_image_le
      _ = k := Finset.card_range k
  have himg : (wordsWith k e).image (climbRot k) ⊆ climbSet k := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hcount : v.toList.count true = e := by simpa [wordsWith] using hv
    have := (climbRot_spec k v (by rw [hcount]; exact he)).1
    simpa [climbSet] using this
  calc (wordsWith k e).card
      ≤ k * ((wordsWith k e).image (climbRot k)).card :=
        Finset.card_le_mul_card_image _ k hfib
    _ ≤ k * (climbSet k).card := Nat.mul_le_mul_left k (Finset.card_le_card himg)
    _ = k * c k := rfl

/-! ### Upper bound -/

/-- e₀(k) = the least e with 2^k < 3^e. -/
theorem exists_e : ∃ e, 2 ^ k < 3 ^ e :=
  ⟨k + 1, by
    calc 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
      _ < 3 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)⟩

noncomputable def e0 : ℕ := Nat.find (exists_e k)

theorem e0_spec : 2 ^ k < 3 ^ e0 k := Nat.find_spec (exists_e k)

theorem e0_min {e : ℕ} (h : 2 ^ k < 3 ^ e) : e0 k ≤ e := Nat.find_min' (exists_e k) h

theorem e0_le (hk : 1 ≤ k) : e0 k ≤ k :=
  e0_min k (Nat.pow_lt_pow_left (by norm_num) (by omega))

/-- 2 e₀ > k, since 3^e ≤ 4^e. -/
theorem two_e0_gt : k < 2 * e0 k := by
  have h := e0_spec k
  have h4 : 3 ^ e0 k ≤ 4 ^ e0 k := Nat.pow_le_pow_left (by norm_num) _
  have : 2 ^ k < 2 ^ (2 * e0 k) := by
    calc 2 ^ k < 3 ^ e0 k := h
      _ ≤ 4 ^ e0 k := h4
      _ = 2 ^ (2 * e0 k) := by rw [pow_mul]; norm_num
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this

theorem climbing_count_ge (hk : 1 ≤ k) (v : List.Vector Bool k) (hv : Climbing v.toList) :
    e0 k ≤ v.toList.count true := by
  have := hv k hk (by simp)
  rw [pc, List.take_of_length_le (by simp)] at this
  exact e0_min k this

/-! ### Identification #{words with e ones} = choose k e -/

theorem count_true_ofFn : ∀ {n : ℕ} (f : Fin n → Bool),
    (List.ofFn f).count true = (Finset.univ.filter (fun i => f i = true)).card := by
  intro n
  induction n with
  | zero => intro f; simp
  | succ n ih =>
    intro f
    rw [List.ofFn_succ, List.count_cons, ih (fun i => f i.succ)]
    simp only [Finset.card_filter, Fin.sum_univ_succ]
    cases f 0 <;> simp [add_comm]

/-- Indicator vector of a subset of positions. -/
def indV (s : Finset (Fin k)) : List.Vector Bool k :=
  List.Vector.ofFn (fun i => decide (i ∈ s))

theorem indV_injective : Function.Injective (indV k) := by
  intro s t hst
  ext i
  have := congrArg (fun v : List.Vector Bool k => v.get i) hst
  simpa [indV] using this

theorem count_indV (s : Finset (Fin k)) : (indV k s).toList.count true = s.card := by
  simp only [indV, List.Vector.toList_ofFn, count_true_ofFn]
  congr 1
  ext i
  simp

theorem wordsWith_eq_image (e : ℕ) :
    wordsWith k e = (Finset.powersetCard e Finset.univ).image (indV k) := by
  ext v
  simp only [wordsWith, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_powersetCard, Finset.subset_univ]
  constructor
  · intro hv
    refine ⟨Finset.univ.filter (fun i => v.get i = true), ?_, ?_⟩
    · have hl : v.toList = List.ofFn v.get := by
        rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]
      rw [← hv, hl, count_true_ofFn]
    · apply List.Vector.ext
      intro i
      simp [indV]
  · rintro ⟨s, hs, rfl⟩
    rw [count_indV]; exact hs

theorem card_wordsWith (e : ℕ) : (wordsWith k e).card = Nat.choose k e := by
  rw [wordsWith_eq_image, Finset.card_image_of_injective _ (indV_injective k),
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-! ### Upper bound -/

theorem choose_antitone_above (_hk : 1 ≤ k) :
    ∀ e, e0 k ≤ e → e ≤ k → Nat.choose k e ≤ Nat.choose k (e0 k) := by
  intro e he
  induction e, he using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ e he ih =>
    intro hek
    have h2 := two_e0_gt k
    have hsym1 : Nat.choose k (e + 1) = Nat.choose k (k - (e + 1)) :=
      (Nat.choose_symm (by omega)).symm
    have hsym2 : Nat.choose k (k - e) = Nat.choose k e := Nat.choose_symm (by omega)
    have hstep : Nat.choose k (k - (e + 1)) ≤ Nat.choose k (k - (e + 1) + 1) :=
      Nat.choose_le_succ_of_lt_half_left (by omega)
    have heq : k - (e + 1) + 1 = k - e := by omega
    rw [heq, hsym2] at hstep
    calc Nat.choose k (e + 1) = Nat.choose k (k - (e + 1)) := hsym1
      _ ≤ Nat.choose k e := hstep
      _ ≤ Nat.choose k (e0 k) := ih (by omega)

open Classical in
theorem climbSet_card_le (hk : 1 ≤ k) :
    (climbSet k).card ≤ ∑ e ∈ Finset.Icc (e0 k) k, (wordsWith k e).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun v => v.toList.count true)
    (t := Finset.Icc (e0 k) k)]
  · apply Finset.sum_le_sum
    intro e _
    apply Finset.card_le_card
    intro v hv
    rw [Finset.mem_filter] at hv
    simp [wordsWith, hv.2]
  · intro v hv
    rw [Finset.mem_coe] at hv
    simp only [climbSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rw [Finset.mem_coe, Finset.mem_Icc]
    refine ⟨climbing_count_ge k hk v hv, ?_⟩
    calc v.toList.count true ≤ v.toList.length := List.count_le_length
      _ = k := by simp

/-- **Upper bound**: c(k) ≤ (k+1) · C(k, e₀). -/
theorem upper_bound (hk : 1 ≤ k) : c k ≤ (k + 1) * Nat.choose k (e0 k) := by
  calc c k = (climbSet k).card := rfl
    _ ≤ ∑ e ∈ Finset.Icc (e0 k) k, (wordsWith k e).card := climbSet_card_le k hk
    _ = ∑ e ∈ Finset.Icc (e0 k) k, Nat.choose k e := by
        apply Finset.sum_congr rfl; intro e _; exact card_wordsWith k e
    _ ≤ (Finset.Icc (e0 k) k).card • Nat.choose k (e0 k) := by
        apply Finset.sum_le_card_nsmul
        intro e he
        rw [Finset.mem_Icc] at he
        exact choose_antitone_above k hk e he.1 he.2
    _ ≤ (k + 1) * Nat.choose k (e0 k) := by
        rw [smul_eq_mul, Nat.card_Icc]
        exact Nat.mul_le_mul_right _ (by omega)

/-- **Lower bound** in binomial form: C(k, e₀) ≤ k · c(k). -/
theorem lower_bound_choose : Nat.choose k (e0 k) ≤ k * c k := by
  rw [← card_wordsWith]
  exact lower_bound k (e0 k) (e0_spec k)

/-- **Theorem B (sandwich)**: C(k,e₀)/k ≤ c(k) ≤ (k+1) C(k,e₀), with
    e₀ = ⌈θk⌉ = the least e with 3^e > 2^k. -/
theorem theoremB (hk : 1 ≤ k) :
    Nat.choose k (e0 k) ≤ k * c k ∧ c k ≤ (k + 1) * Nat.choose k (e0 k) :=
  ⟨lower_bound_choose k, upper_bound k hk⟩

end CollatzB

#print axioms CollatzB.rotate_climbing
#print axioms CollatzB.lower_bound_choose
#print axioms CollatzB.upper_bound
#print axioms CollatzB.theoremB
