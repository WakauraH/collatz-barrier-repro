"""exp22_close_chain.py — 鎖を閉じる: 小 |μ| の capped ℓ¹ 汎関数 × 鋭利版 Tao 積率。

r(μ) = μ·log₂3 + log₂(2^{1−μ}−1)  (μ < 0 で r > 0; μ = λ† で r = I₀)
制約 (深部帯 δ = |u|/m ≥ ε): r(μ) + |μ|·δ ≤ a(δ)  (a = 測定済み Tao 積率)
seam (k = O(1), δ ≈ α): r(μ) + |μ|·α ≤ a_seam
これが成立する最大の r を求める。成立すれば「無条件指数減衰 δ_m ≤ 2^{−rm}」の
数値的骨組みが完成 (残る厳密化は a(δ) の一様証明のみ)。

Part 1: seam と追加帯の率測定 (m = 240): k = 0, ±16, 0.2mα, 0.5mα, 0.8mα
Part 2: 実行可能性の最適化と結論
"""
import math

from exp21_tao_product import tao_bound_rate

LOG2_3 = math.log2(3)
I0 = 0.0793186127748554


def r_of_mu(mu):
    return mu * LOG2_3 + math.log2(2 ** (1 - mu) - 1)


if __name__ == "__main__":
    m = 240
    print("Part 1: 追加帯の率 (m=240)")
    pts = []
    for tag, k in [("seam k=0 (δ=α)", 0), ("k=16", 16), ("k=-16 (逆冪)", -16),
                   ("k=0.2mα (δ=0.8α)", int(0.2 * m * LOG2_3)),
                   ("k=0.5mα (δ=0.5α)", int(0.5 * m * LOG2_3)),
                   ("k=0.8mα (δ=0.2α)", int(0.8 * m * LOG2_3))]:
        a = tao_bound_rate(m, k)
        delta = abs(k - m * LOG2_3) / m
        pts.append((delta, a, tag))
        print(f"  {tag:22s}: a = {a:.4f}  (δ = {delta:.3f})")
    # exp21 の m=240 測定値も制約に追加
    for delta, a in [(0.30, 0.1078), (0.15, 0.0812), (0.05, 0.0636)]:
        pts.append((delta, a, f"below δ={delta}"))

    print("\nPart 2: 実行可能性最適化")
    best = None
    for mu100 in range(-1, -45, -1):
        mu = mu100 / 100.0
        r = r_of_mu(mu)
        # 全深部制約: r + |μ|δ ≤ a − margin (margin 0.005)
        ok = all(r + abs(mu) * d <= a - 0.005 for d, a, _ in pts)
        if ok and (best is None or r > best[1]):
            best = (mu, r)
    if best:
        mu, r = best
        print(f"  実行可能: μ = {mu:.2f}, 無条件候補率 r = {r:.4f} bits/level "
              f"(I₀ = {I0:.4f} の {100*r/I0:.0f}%)")
        print("  制約検証:")
        for d, a, tag in sorted(pts):
            slack = a - (r + abs(mu) * d)
            print(f"    δ={d:.3f} ({tag:22s}): a={a:.4f}  要求={r + abs(mu)*d:.4f}  "
                  f"余裕={slack:+.4f}")
    else:
        print("  実行不能 — 測定済み率では鎖は閉じない")
