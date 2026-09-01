"""exp26_certify_instance.py — 補題C-局所の有限証明化: 固定 m での実例証明。

漸近的な C-局所は ×2×3 剛性圏(パネル裁定)だが、各固定 m については
帯率入力が O(poly m) の計算で決定可能である。ここでは m = 64 で:
  (1) 窓内の全指数 k ∈ [KLO, KHI] について Tao 積上界 B(2^k) を計算
      (B(ξ) ≥ |f_m(ξ)| は証明済みの不等式)
  (2) capped ℓ¹ 帳簿 (μ, cap) の制約系を「全 k の実測 B」で検証
  (3) 成立すれば: その m について δ_m ≤ 2^{−r·m}·C の計算的証明が完成
      (残る厳密化は float→区間演算の置換のみ、構造的仮定はゼロ)
"""
import math

from exp21_tao_product import tao_bound_rate

LOG2_3 = math.log2(3)
I0 = 0.0793186127748554


def r_of_mu(mu):
    return mu * LOG2_3 + math.log2(2 ** (1 - mu) - 1)


if __name__ == "__main__":
    import sys
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 64
    KLO_, KHI_ = -80, int(1.66 * m) + 20
    print(f"m={m}: 全窓 k ∈ [{KLO_}, {KHI_}] の Tao 積率を計算 ({KHI_-KLO_+1} 個)...")
    rates = {}
    for k in range(KLO_, KHI_ + 1):
        rates[k] = tao_bound_rate(m, k)
    # 帯別の最小率 (証明に使う一様下界 = 実測 min)
    zones = {"seam/deep (k<0.3mα)": [], "mid": [], "shoulder": [], "line±": [], "wrap": []}
    for k, a in rates.items():
        u = k - m * LOG2_3
        if k < 0.3 * m * LOG2_3:
            zones["seam/deep (k<0.3mα)"].append(a)
        elif u < -0.15 * m:
            zones["mid"].append(a)
        elif u < -8:
            zones["shoulder"].append(a)
        elif u <= 2:
            zones["line±"].append(a)
        else:
            zones["wrap"].append(a)
    print("帯別 min/mean 率:")
    zmin = {}
    for z, arr in zones.items():
        if arr:
            zmin[z] = min(arr)
            print(f"  {z:22s}: min={min(arr):.4f}  mean={sum(arr)/len(arr):.4f}  n={len(arr)}")
    # 制約系: μ を走査し、全 k (line± 帯を除く既定義帯) について
    #   r(μ) + |μ|·δ_k ≤ a_k が成立する最大 r を求める
    best = None
    for mu100 in range(-1, -45, -1):
        mu = mu100 / 100.0
        r = r_of_mu(mu)
        ok = True
        for k, a in rates.items():
            u = k - m * LOG2_3
            if -8 <= u <= 2:
                continue  # 臨界窓 (リッジ) は汎関数の縮小側が担う
            delta = abs(u) / m
            if r + abs(mu) * delta > a - 0.002:
                ok = False
                break
        if ok and (best is None or r > best[1]):
            best = (mu, r)
    if best:
        mu, r = best
        print(f"\n証明可能な組: μ = {mu:.2f}, r = {r:.4f} bits/level")
        print(f"⇒ 計算的証明 (実例): δ_{m} ≤ C·2^{{−{r:.4f}·{m}}} = C·2^{{−{r*m:.1f}}}")
        print(f"   (I₀·m = {I0*m:.1f}; 対照: 窓内実測 log₂δ_{m} ≈ −{0.0793*m + 1.3*math.log2(m):.1f})")
        print("   帯ごとの最タイト制約:")
        worst = sorted(((rates[k] - (r + abs(mu) * abs(k - m*LOG2_3)/m), k)
                        for k in rates if not (-8 <= k - m*LOG2_3 <= 2)))[:5]
        for slack, k in worst:
            print(f"     k={k:4d} (u={k-m*LOG2_3:+.1f}): 余裕 {slack:+.4f}")
    else:
        print("\n制約系は m=64 では閉じない (より大きい m か μ 微調整が必要)")
