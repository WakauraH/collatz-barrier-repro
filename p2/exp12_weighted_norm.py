"""exp12_weighted_norm.py — サイクル1実行: 重み付き作用素ノルム縮小の補題化。

補題 (臨界線以下の縮小): u = k − m·log₂3、重み w(u) = 2^{λu} (u ≤ 0)、
1 レベルの重み付き行和は位相を捨てても
    f(λ) = Σ_a 2^{−a} 2^{λ(log₂3−a)} = 3^λ/(2^{1+λ}−1),
    min_λ f(λ) = 2^{−(1−H(θ))/θ} = 2^{−I₀},  λ* : 2^{1+λ*} = log₂3/(log₂3−1)。
検証1: この恒等式を 40 桁で確認 (F1 殺し条件)。
検証2: 実データ (リスケール格子 m ≤ 400) で
    N_m = max_{u≤0} |g_m(k)|·2^{λ* u}  (臨界線以下の重み付きノルム)
    A_m = max_{u>0} |g_m(k)|           (臨界線より上の sup)
  を測り、(i) N_m·2^{I₀ m} が多項式増大に留まるか (F2 殺し条件)、
  (ii) 境界項 A_m が N_m に対しどう振る舞うか (F3 評価) を判定する。
"""
import math
from decimal import Decimal, getcontext

import numpy as np

getcontext().prec = 50
AMAX = 64
KLO = -96
LOG2_3 = math.log2(3)


def part1():
    ln2, ln3 = Decimal(2).ln(), Decimal(3).ln()
    L = ln3 / ln2                       # log2 3
    lam = ((L / (L - 1)).ln() / ln2) - 1   # 2^{1+λ*} = L/(L−1)
    # f(λ*) = 3^{λ*}/(2^{1+λ*}−1)
    f = (lam * ln3).exp() / ((L / (L - 1)) - 1)
    theta = ln2 / ln3
    H = -(theta * (theta.ln() / ln2) + (1 - theta) * ((1 - theta).ln() / ln2))
    I0 = (1 - H) / theta
    lhs = -(f.ln() / ln2)
    print(f"λ* = {float(lam):.10f}")
    print(f"−log₂ min f = {lhs}")
    print(f"(1−H(θ))/θ  = {I0}")
    diff = abs(lhs - I0)
    print(f"差 = {float(diff):.2e}  (恒等式: F1 不成立 = A 続行)")
    assert diff < Decimal(10) ** -40
    return float(lam), float(I0)


def part2(lam, I0, M_TOP=400):
    KHI = int(1.66 * M_TOP) + 40
    W = KHI - KLO + 1
    g = np.ones(W, dtype=np.complex128)
    wts = np.array([2.0 ** -a for a in range(1, AMAX + 1)])
    ks = np.arange(KLO, KHI + 1, dtype=float)
    logscale = 0.0
    rows = []
    for m in range(1, M_TOP + 1):
        M3 = 3 ** m
        inv2 = pow(2, -1, M3)
        pw = np.empty(W, dtype=np.float64)
        v = pow(inv2, -KLO, M3)
        for i in range(W):
            pw[i] = v / M3
            v = (v * 2) % M3
        ph = np.exp(2j * np.pi * pw)
        t = ph * g
        gn = np.zeros(W, dtype=np.complex128)
        for a in range(1, AMAX + 1):
            gn[a:] += wts[a - 1] * t[:-a]
        g = gn
        mags = np.abs(g)
        s = mags.max()
        u = ks - m * LOG2_3
        below = u <= 0
        above = (~below) & (ks >= 0)
        N = (mags[below] * np.exp2(lam * u[below])).max()
        A = mags[above].max() if above.any() else 0.0
        rows.append((m, logscale + math.log2(N),
                     (logscale + math.log2(A)) if A > 0 else None))
        g /= s
        logscale += math.log2(s)
    print("\nm, log2 N_m + I0·m (有界/多項式なら F2 不成立), log2 A_m − log2 N_m:")
    for (m, lN, lA) in rows:
        if m % 50 == 0:
            gap = (lA - lN) if lA is not None else float("nan")
            print(f"  m={m:4d}: log2N+I0m = {lN + I0*m:8.3f}   A/N gap = {gap:7.2f} bits")
    # F2 判定: log2N + I0 m の増大が O(log m) か
    msel = [r for r in rows if r[0] >= 100]
    xs = np.array([math.log2(r[0]) for r in msel])
    ys = np.array([r[1] + I0 * r[0] for r in msel])
    slope = np.polyfit(xs, ys, 1)[0]
    print(f"\nF2 判定: log2(N_m·2^(I0 m)) ≈ {slope:.2f}·log2 m + const "
          f"(多項式増大 ⇒ F2 不成立、還元は空虚でない)")
    return rows


if __name__ == "__main__":
    print("=== 検証1: 縮小率恒等式 (F1) ===")
    lam, I0 = part1()
    print("\n=== 検証2: 実データでの重み付きノルム (F2/F3) ===")
    part2(lam, I0)
