"""exp21_tao_product.py — Tao §7 の積評価の鋭利版 DP を窓外周波数で線形化する。

Tao (7.5): |S_χ(m)| ≤ E Π_{j∈[m/2]} |f(3^{2j−2} 2^{−b_{[1,j]}}, b_j)|,
  b_j iid Pascal(2,1/2) (P(b)= (b−1)/2^b, b ≥ 2),
  f(x,b) = (1/(b−1)) Σ_{t=1}^{b−1} χ(x(2^t+3)),  χ(y) = e(−ξ y/3^m)。
ξ = 2^k mod 3^m に対し右辺を l = b_{[1,j]} 上の DP で厳密計算し、
  rate(u) := −log₂(bound)/m  (u = k − m·log₂3)
を測る。Tao の白点補題 (b=3 のみ・ε³ 係数) は率 ~10⁻⁶ しか出さないが、
全 b の鋭い積なら窓外で率 ≫ I₀ = 0.0793 が出るか — これが (W_β) 到達可能性の判定。
検算: bound ≥ |f_m(ξ)| なので ridge では rate ≤ 0.0793 に落ちるはず (整合性)。
"""
import cmath
import math

import numpy as np

LOG2_3 = math.log2(3)
I0 = 0.0793186127748554
BMAX = 40
PRUNE = 1e-22


def tao_bound_rate(m: int, k: int) -> float:
    M3 = 3 ** m
    inv2 = pow(2, -1, M3)
    Pb = [0.0] * (BMAX + 1)
    for b in range(2, BMAX + 1):
        Pb[b] = (b - 1) / 2.0 ** b
    # pow2[e] = 2^e mod 3^m for e in [k - lmax - BMAX, k]
    lmax = 3 * m + 80
    pows = {}
    v = pow(2, k, M3) if k >= 0 else pow(inv2, -k, M3)
    pows[k] = v
    for e in range(k - 1, k - lmax - BMAX - 1, -1):
        v = (v * inv2) % M3
        pows[e] = v
    pow3 = [1] * (m + 2)
    for i in range(1, m + 2):
        pow3[i] = (pow3[i - 1] * 3) % M3
    smalls = [(2 ** t + 3) for t in range(1, BMAX)]
    V = {0: 1.0}
    logscale = 0.0
    for j in range(1, m // 2 + 1):
        p3 = pow(3, 2 * (j - 1), M3)
        nxt = {}
        for l, val in V.items():
            for b in range(2, BMAX + 1):
                l2 = l + b
                base = (pows[k - l2] * p3) % M3   # ξ·x = 3^{2j−2}·2^{k−l2} mod 3^m
                s = 0j
                for t in range(1, b):
                    y = (base * smalls[t - 1]) % M3
                    s += cmath.exp(-2j * math.pi * y / M3)
                w = abs(s) / (b - 1)
                nxt[l2] = nxt.get(l2, 0.0) + val * Pb[b] * w
        mx = max(nxt.values())
        V = {l: x for l, x in nxt.items() if x > PRUNE * mx}
        logscale += math.log2(mx)
        for l in V:
            V[l] /= mx
    total = logscale + math.log2(sum(V.values()))
    return -total / m


if __name__ == "__main__":
    print("Tao 積評価 (鋭利版 DP) の率 rate(u) [bits/level]:")
    print("  目標: 窓外で rate >> I0 = 0.0793 / ridge では rate <= 0.0793 (検算)")
    for m in (80, 160, 240):
        row = []
        for tag, k in [("u=-0.3m", int(m * LOG2_3 - 0.30 * m)),
                       ("u=-0.15m", int(m * LOG2_3 - 0.15 * m)),
                       ("u=-0.05m", int(m * LOG2_3 - 0.05 * m)),
                       ("ridge(u≈-7)", int(m * LOG2_3 - 7)),
                       ("u=+0.05m", int(m * LOG2_3 + 0.05 * m)),
                       ("u=+0.15m", int(m * LOG2_3 + 0.15 * m))]:
            r = tao_bound_rate(m, k)
            row.append(f"{tag}: {r:.4f}")
        print(f"  m={m:3d}:  " + "  ".join(row))
