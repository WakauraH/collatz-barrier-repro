"""exp19_wrap_budget.py — 4重転送の wrap 項評価。

構造ノート: 周辺和への Jensen は T(m) ≤ 2^{−I₀}T(m−1) しか与えない(厳密だが弱い)。
真の縮小 2^{−4I₀} との差は 4 本の付値歩みの脱相関が担い、wrap 項は相関テンソルの
上側セルとして入る。よって評価対象は:
  (1) 重み付き ℓ⁴ 汎関数 T_λ(m) = Σ_k 2^{λ†u}|g|⁴ の実効縮小率と wrap 部
      (u>0) の予算比 W(m)
  (2) 指数格子上の相関 Γ(d) = |Σ g(k)ḡ(k−d)|/Σ|g|² — 相関長 O(1) なら
      4 歩みは実効独立で 4I₀ が出る (テンソル縮小の入力)
  (3) wrap セル位相 {2^k mod 3^m}/3^m (u ∈ (0,40]) の等分布性 (KS 統計)
"""
import math

import numpy as np

AMAX = 60
KLO = -96
LOG2_3 = math.log2(3)
I0 = 0.0793186127748554
LAM_DAG = -0.4380326593  # λ† (ℓ⁴ 和汎関数の最適重み指数)


def run(M_TOP=400):
    KHI = int(1.9 * M_TOP) + 40
    W = KHI - KLO + 1
    g = np.ones(W, dtype=np.complex128)
    wts = np.array([2.0 ** -a for a in range(1, AMAX + 1)])
    ks = np.arange(KLO, KHI + 1, dtype=float)
    logscale = 0.0
    prevT = None
    print("m, 実効縮小率 −log2[T(m)/T(m−1)] (目標 4I0=0.3173), wrap予算 W(m)")
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
        u = ks - m * LOG2_3
        Vw = np.exp2(LAM_DAG * u)
        contrib = Vw * mags ** 4
        T = float(contrib.sum())
        wrap_share = float(contrib[u > 0].sum()) / T
        l2T = 4 * logscale + math.log2(T)
        if m in (100, 150, 200, 250, 300, 350, 400):
            rate = -(l2T - prevT[1]) / (m - prevT[0])
            print(f"  m={m:3d}: rate={rate:.5f}   W(m)={wrap_share:.4f}")
        if m in (50,) or m % 50 == 0:
            prevT = (m, l2T)
        if prevT is None:
            prevT = (m, l2T)
        # (2)(3) チェックポイント
        if m in (200, 400):
            # 相関 Γ(d)
            num0 = float((mags ** 2).sum())
            print(f"    m={m} 相関 Γ(d):", end=" ")
            for d in (1, 2, 3, 5, 8, 12):
                c = abs(np.vdot(g[d:], g[:-d]))
                print(f"d={d}:{c/num0:.3f}", end="  ")
            print()
            # wrap 位相の等分布 (u ∈ (0,40])
            sel = (u > 0) & (u <= 40)
            phases = np.sort(pw[sel] % 1.0)
            n = len(phases)
            ks_stat = np.max(np.abs(phases - (np.arange(1, n + 1) / n)))
            print(f"    m={m} wrap位相 KS 統計 = {ks_stat:.4f} "
                  f"(n={n}; 一様なら ~{1.36/math.sqrt(n):.3f} 以下で5%水準)")
        s = mags.max()
        g /= s
        logscale += math.log2(s)


if __name__ == "__main__":
    run(400)
