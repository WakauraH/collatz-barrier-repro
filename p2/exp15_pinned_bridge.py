"""exp15_pinned_bridge.py — サイクル4実行: ピン留めブリッジ非消滅の事前登録判定。

対象: amp_{m−5}(k*) = E[e(x Σ_{i≤m−5} 3^{i−1}2^{−A_i}); A_{m−5} = k*]  (x = 2^{k*}/3^m)
測定:
  S1/S2: |amp| のレート a (フィット −log₂|amp| = a·m + β·log₂m + c, m ∈ [200,400])
         判定: a ∈ [I₀−0.001, I₀+0.002] (片側基準)
  S3   : 位相保持率 R_m = |amp_ph| / P(A_{m−5} = k*) が m ∈ [200,400] で
         変動 <20% かつ > 0.05 (終端位相因子の非零性)
  F1: a > I₀+0.003 / F2: (別途) / F3: R_m < 0.01
"""
import math

import numpy as np

AMAX = 64
KLO = -96
LN2, LN3 = math.log(2), math.log(3)
I0 = 0.0793186127748554


def lattice_kstars(M_TOP=400):
    KHI = int(1.66 * M_TOP) + 40
    W = KHI - KLO + 1
    g = np.ones(W, dtype=np.complex128)
    wts = np.array([2.0 ** -a for a in range(1, AMAX + 1)])
    kstars = {}
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
        i0x = -KLO
        kstars[m] = i0x + int(np.argmax(mags[i0x:])) + KLO
        g /= mags.max()
    return kstars


def pinned_amp(m, k, with_phase=True):
    """amp_{m−5}(k) を DP で。返り値: 複素値 (絶対スケール)。"""
    J = m - 5
    amp = np.zeros(k + 1, dtype=np.complex128)
    amp[0] = 1.0
    wts = np.array([2.0 ** -a for a in range(1, AMAX + 1)])
    A_idx = np.arange(k + 1, dtype=float)
    for j in range(1, J + 1):
        if with_phase:
            expo = (k - A_idx) * LN2 + (j - 1 - m) * LN3
            arg = np.where(expo > -42, np.exp(np.clip(expo, None, 5)), 0.0)
            phase = np.exp(2j * np.pi * arg)
        else:
            phase = np.ones(k + 1, dtype=np.complex128)
        nxt = np.zeros(k + 1, dtype=np.complex128)
        for a in range(1, AMAX + 1):
            if a > k:
                break
            nxt[a:] += wts[a - 1] * amp[:-a] * phase[a:]
        amp = nxt
    return amp[k]


if __name__ == "__main__":
    print("k* 表を構築中 (m<=400)...")
    kst = lattice_kstars(400)
    ms = list(range(40, 401, 40)) + [360, 400]
    ms = sorted(set(ms))
    rows = []
    print("m, k*, −log2|amp|−I0m, R_m = |amp|/P(pinned):")
    for m in ms:
        k = kst[m]
        a_ph = pinned_amp(m, k, True)
        a_pr = pinned_amp(m, k, False)
        P = abs(a_pr)
        R = abs(a_ph) / P if P > 0 else float("nan")
        excess = -math.log2(abs(a_ph)) - I0 * m
        rows.append((m, excess, R))
        print(f"  m={m:3d}: k*={k:3d}  excess={excess:7.3f}  R_m={R:.4f}")
    # S1/S2: フィット (m >= 200)
    sel = [r for r in rows if r[0] >= 200]
    msv = np.array([r[0] for r in sel], dtype=float)
    ys = np.array([r[1] + I0 * r[0] for r in sel])  # = −log2|amp|
    X = np.vstack([msv, np.log2(msv), np.ones_like(msv)]).T
    coef, *_ = np.linalg.lstsq(X, ys, rcond=None)
    a_fit, beta = coef[0], coef[1]
    Rs = [r[2] for r in sel]
    var = (max(Rs) - min(Rs)) / max(Rs)
    print(f"\nS1/S2: レート a = {a_fit:.5f} (基準 [I0−0.001, I0+0.002] = "
          f"[{I0-0.001:.5f}, {I0+0.002:.5f}]), 冪 β = {beta:.2f}")
    print(f"S3: R_m (m>=200) = {['%.4f' % r for r in Rs]}  変動 {100*var:.1f}%  "
          f"min = {min(Rs):.4f} (>0.05 で合格, <0.01 で F3)")
    ok = (I0 - 0.001 <= a_fit <= I0 + 0.002) and var < 0.20 and min(Rs) > 0.05
    f1 = a_fit > I0 + 0.003
    f3 = min(Rs) < 0.01
    print(f"\n判定: {'S 成立 — 単一ピン留めブリッジが 2^(−I0 m−o(m)) を達成、非消滅は数値確立' if ok else ('F1 発火' if f1 else ('F3 発火' if f3 else '境界的 — 素描は分離仮説を明示条件として記述'))}")
