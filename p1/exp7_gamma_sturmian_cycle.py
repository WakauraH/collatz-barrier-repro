"""exp7_gamma_sturmian_cycle.py — 3課題の実行:
 (2) γ = H(θ) の完全証明の計算検証 (回転補題 + 上下界の非漸近版)
 (3) Sturmian 変調転送分解の厳密検証と CF スケールでの揺らぎ測定
 (4) 周期下界の片側 (上側) 最良近似による改良

(2) 定理: C(k,⌈θk⌉)/k ≤ c(k) ≤ (k+1)·C(k,⌈θk⌉),  θ = log₃2。
    ゆえに γ = lim log₂c(k)/k = H(θ)。
    下界の核 (回転補題): 総和 e − θk > 0 の任意の 0/1 列は、接頭辞和がすべて
    正 (= climbing) となる巡回回転を少なくとも 1 つ持つ (最小到達点の直後から
    開始する回転)。ここでは k ≤ 16 の全列で検証し、上下界を k ≤ 1600 で検証。

(3) 定理 (構成的): σ_j = ⌊θ(j+1)⌋ − ⌊θj⌋ (θ = log₃2 の Sturmian 語) とし、
    超過 d_j = e_j − ⌊θj⌋ − 1 ≥ 0 の歩みは
      σ=0: d → d (b=0) / d+1 (b=1),   σ=1: d → d−1 (b=0, d≥1) / d (b=1)
    で与えられ、c(k) = (この Sturmian 駆動歩みの非負滞在路の総数)。
    DP で厳密一致を検証し、b̃(k) = log₂c(k) − log₂C(k,⌈θk⌉) ∈ [−log₂k, log₂(k+1)]
    (証明済み) の実揺らぎを log₃2 の収束分母スケールで出力。

(4) 片側改良: 周期の必要条件は ‖kθ'‖⁺ = ⌈kθ'⌉ − kθ' ≤ k·δ (θ' = log₂3)。
    上側最良近似の梯子 (mediant 歩み) により、区間 [a_i, a_{i+1}) では
    ‖kθ'‖⁺ ≥ η_{a_i}。すべての k < K* を排除する最大 K* を計算し、
    従来の両側評価 (M>2^68: 8.96e9) と比較する。
"""
import math
from decimal import Decimal, getcontext
from fractions import Fraction

from certtree import climbing_counts_dp

getcontext().prec = 130


def floor_theta_j(j: int) -> int:
    """⌊j·log₃2⌋ = max{e : 3^e <= 2^j} (厳密整数比較)。"""
    e = int(j * 0.63093) - 2
    while 3 ** (e + 1) <= 2 ** j:
        e += 1
    return e


# ---------- (2) ----------
def climbing_str(bits, k):
    e = 0
    for j in range(1, k + 1):
        e += bits[j - 1]
        if 3 ** e <= 2 ** j:  # e_j > θj の否定
            return False
    return True


def verify_rotation_lemma(kmax=16):
    for k in range(2, kmax + 1):
        emin = floor_theta_j(k) + 1  # e > θk ⟺ e >= ⌊θk⌋+1
        for x in range(1 << k):
            bits = [(x >> i) & 1 for i in range(k)]
            if sum(bits) < emin:
                continue
            assert any(climbing_str(bits[r:] + bits[:r], k) for r in range(k)), (k, x)


# ---------- (3) ----------
def sturmian_dp(K: int):
    """Sturmian 駆動の非負歩みで c(k) を再構成。"""
    c = [0] * (K + 1)
    cur = {}
    # j=1: e_1 > θ ⟺ e_1 = 1 (⌊θ⌋=0 ⇒ d_1 = e_1 - 1 >= 0 ⇒ b_1 = 1)
    cur[0] = 1
    c[1] = 1
    for j in range(1, K):
        sigma = floor_theta_j(j + 1) - floor_theta_j(j)
        nxt = {}
        for d, cnt in cur.items():
            for b in (0, 1):
                d2 = d + b - sigma
                if d2 >= 0:
                    nxt[d2] = nxt.get(d2, 0) + cnt
        cur = nxt
        c[j + 1] = sum(cur.values())
    return c


# ---------- (4) ----------
def one_sided_cycle_bound(log2M: int):
    theta = Decimal(3).ln() / Decimal(2).ln()
    guard = Decimal(10) ** -110
    M = Decimal(2) ** log2M
    delta = (1 + 1 / (3 * M)).ln() / Decimal(2).ln() + guard

    # mediant 梯子: a = 上側 (‖aθ‖+ = eta_a), b = 下側 ({bθ} = eta_b)
    one = Decimal(1)
    frac1 = theta - int(theta)          # {θ} = 0.585
    a, eta_a = 1, one - frac1           # 0.41504
    b, eta_b = 1, frac1
    kmin = None
    while True:
        if eta_a > eta_b:
            a_next = a + b
            eta_next = eta_a - eta_b
            # 上側最良近似の更新: 区間 [a, a_next) では ‖kθ‖+ >= eta_a
            if Decimal(a_next - 1) * delta >= eta_a - guard:
                kmin = min(int((eta_a - guard) / delta), a_next - 1)
                break
            a, eta_a = a_next, eta_next
        else:
            b, eta_b = a + b, eta_b - eta_a
        if a > 10 ** 14:
            kmin = 10 ** 14
            break
    return kmin


if __name__ == "__main__":
    theta = math.log(2) / math.log(3)

    print("(2) γ = H(θ) の完全証明の検証")
    verify_rotation_lemma(16)
    print("  回転補題: k<=16 の全列で成立 (e>θk ⇒ climbing 回転が存在)")
    K = 1600
    c = climbing_counts_dp(K)
    for k in range(2, K + 1):
        e = floor_theta_j(k) + 1
        binom = math.comb(k, e)
        assert c[k] * k >= binom, k          # 下界 C/k <= c(k)
        assert c[k] <= (k + 1) * binom, k    # 上界
    print(f"  非漸近上下界 C(k,⌈θk⌉)/k <= c(k) <= (k+1)C(k,⌈θk⌉): k<=({K}) 全数成立")
    print(f"  ⇒ γ = H(θ) = {(-theta*math.log2(theta)-(1-theta)*math.log2(1-theta)):.9f} 確定\n")

    print("(3) Sturmian 変調転送分解")
    cs = sturmian_dp(400)
    assert all(cs[k] == c[k] for k in range(1, 401))
    print("  Sturmian 駆動 DP と c(k) の厳密一致: k<=400 ✓")
    print("  b̃(k) = log₂c(k) − log₂C(k,⌈θk⌉)  (証明済み範囲 [−log₂k, +log₂(k+1)]):")
    qs = [q for q in (2, 3, 8, 19, 65, 84, 485, 1000, 1569) if q <= K]
    for q in qs:
        e = floor_theta_j(q) + 1
        bt = math.log2(c[q]) - math.log2(math.comb(q, e))
        print(f"    k={q:5d} (収束分母級): b̃ = {bt:+.4f}  範囲 [-{math.log2(q):.2f}, +{math.log2(q+1):.2f}]")
    print()

    print("(4) 周期下界の片側改良")
    for log2M in (68, 71):
        kmin = one_sided_cycle_bound(log2M)
        print(f"  M > 2^{log2M}: 奇数ステップ数 k >= {kmin:,} "
          f"(従来両側: {'8,963,457,696' if log2M==68 else '32,670,997,555'})")
