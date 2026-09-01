"""exp20_l1_functional.py — 残る解析作業: ℓ¹ 線形汎関数による (Lα) の最終簡約の検証。

定理候補 (条件付き帰着定理):
  仮定 (W_β): ある β > I₀ と窓幅 U₀, U₁ = O(log m) があり、
    |g_m(k)| ≤ C·2^{−βm}  (すべての k ∉ (mα − U₀, mα + U₁)、α = log₂3)
  結論: δ_m ≤ C′·poly(m)·2^{−I₀m}。
証明の骨子 (線形・位相不要):
  N₁(m) = Σ_k 2^{λ†·u(k)}|g_m(k)| (u = k − mα, λ† = −0.4380 < 0) について
  行和恒等式 Σ_a 2^{−a} 2^{λ†(a−α)} = 3^{−λ†}/(2^{1−λ†}−1) = 2^{−I₀} (exp18 検証済み)
  により、指数円の継ぎ目を除き N₁(m) ≤ 2^{−I₀} N₁(m−1) + (継ぎ目・深部注入)。
  注入は (W_β) の下で Σ_t 2^{−I₀(m−t)}·2^{(0.438·U₀/m 相当)t}·2^{−βt} で総和可能
  (β > I₀ が要点; 実測 wild 減衰 0.79 に対し要求は 0.0794 — 10 倍の余裕)。
  最後に δ_m ≤ N₁(m)/2^{λ†u*} = N₁(m)·2^{−3.07} (u* ≈ −7)。

数値検証:
  (1) N₁ の per-level 縮小率 → I₀ = 0.07932 bits (片側)
  (2) N₁ の質量の窓集中 (|u| ≤ 20 が何割か)
  (3) δ_m ≤ N₁·2^{−λ†u*} の整合 (比が O(1) で安定するか)
"""
import math

import numpy as np

AMAX = 60
KLO = -96
LOG2_3 = math.log2(3)
I0 = 0.0793186127748554
LAM = -0.4380326593


def run(M_TOP=400):
    KHI = int(1.9 * M_TOP) + 40
    W = KHI - KLO + 1
    g = np.ones(W, dtype=np.complex128)
    wts = np.array([2.0 ** -a for a in range(1, AMAX + 1)])
    ks = np.arange(KLO, KHI + 1, dtype=float)
    logscale = 0.0
    prev = None
    print("m, N₁縮小率(bits, Δ50), 窓集中率(|u|≤20), δ·2^{−λ†u*}/N₁:")
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
        Wt = np.exp2(LAM * u)
        contrib = Wt * mags
        N1 = float(contrib.sum())
        l2N1 = logscale + math.log2(N1)
        if m in (100, 150, 200, 250, 300, 350, 400):
            rate = -(l2N1 - prev[1]) / (m - prev[0])
            conc = float(contrib[np.abs(u) <= 20].sum()) / N1
            # δ と N₁ の関係
            i0x = -KLO
            imax = i0x + int(np.argmax(mags[i0x:]))
            delta_rel = mags[imax]
            ustar = ks[imax] - m * LOG2_3
            ratio = delta_rel * 2.0 ** (-LAM * ustar) / N1
            print(f"  m={m:3d}: rate={rate:.5f}  窓集中={conc:.4f}  "
                  f"δ/(N₁·2^(λ†u*))={ratio:.4f}  (u*={ustar:.1f})")
        if m % 50 == 0 or prev is None:
            prev = (m, l2N1)
        s = mags.max()
        g /= s
        logscale += math.log2(s)


if __name__ == "__main__":
    run(400)
