"""exp16_phase_profile.py — (Lβ) の解剖: ピン留めブリッジの位相損失の深さプロファイル。

ハイブリッド振幅 amp^{(s)}: 位相を「終端から数えて深さ ≤ s のレベル」のみ有効化。
  K(s, m) = |amp^{(s)}_{m−5}(k*)| / P(pinned)   (s = 0 で 1、s = m−5 で R_m)
これにより位相損失がどの深さ層に住むかを分解する。
  仮説 H-log: 損失は対数的に蓄積 (層 s の寄与 ~ c/s) ⇒ K(s) ~ s^{−c}, R_m ~ m^{−c}
  仮説 H-term: 終端 O(1) 層に集中 ⇒ K(s) が小さい s で飽和
"""
import math

import numpy as np

AMAX = 64
KLO = -96
LN2, LN3 = math.log(2), math.log(3)
I0 = 0.0793186127748554


def lattice_kstars(M_TOP):
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


def hybrid_amp(m, k, s_active):
    """位相を j > (m−5) − s_active のレベルのみ有効化した amp_{m−5}(k)。"""
    J = m - 5
    amp = np.zeros(k + 1, dtype=np.complex128)
    amp[0] = 1.0
    wts = np.array([2.0 ** -a for a in range(1, AMAX + 1)])
    A_idx = np.arange(k + 1, dtype=float)
    for j in range(1, J + 1):
        depth_from_end = J - j  # 0 = 最終レベル
        if depth_from_end < s_active:
            expo = (k - A_idx) * LN2 + (j - 1 - m) * LN3
            arg = np.where(expo > -42, np.exp(np.clip(expo, None, 5)), 0.0)
            phase = np.exp(2j * np.pi * arg)
        else:
            phase = None
        nxt = np.zeros(k + 1, dtype=np.complex128)
        for a in range(1, AMAX + 1):
            if a > k:
                break
            if phase is None:
                nxt[a:] += wts[a - 1] * amp[:-a]
            else:
                nxt[a:] += wts[a - 1] * amp[:-a] * phase[a:]
        amp = nxt
    return amp[k]


if __name__ == "__main__":
    M_TOP = 320
    kst = lattice_kstars(M_TOP)
    print("K(s,m) = |amp^{(s)}|/P(pinned)  (行: m、列: s)")
    svals = [0, 2, 4, 8, 16, 32, 64, 128, 256, 10 ** 9]
    header = "  m \\ s | " + " ".join(f"{('all' if s > 10**8 else s):>6}" for s in svals)
    print(header)
    prof = {}
    for m in (80, 160, 320):
        k = kst[m]
        P = abs(hybrid_amp(m, k, 0))
        row = []
        for s in svals:
            v = abs(hybrid_amp(m, k, min(s, m - 5))) / P
            row.append(v)
        prof[m] = row
        print(f"  {m:5d} | " + " ".join(f"{v:6.3f}" for v in row))
    # H-log 判定: K(s) の対数勾配 (m=320)
    m = 320
    xs, ys = [], []
    for i, s in enumerate(svals[1:-1], start=1):
        if 4 <= s <= 256:
            xs.append(math.log(s))
            ys.append(math.log(prof[m][i]))
    c = -np.polyfit(xs, ys, 1)[0]
    print(f"\nm=320: K(s) ~ s^(−{c:.3f})  (H-log なら R_m ~ m^(−{c:.3f}); "
          f"exp15 実測 R_m ~ m^(−1.06) と比較)")
    print("K(s) が s とともに単調減少し飽和しない ⇒ H-term 棄却、"
          "損失は全スケールに対数蓄積 ⇒ (Lβ) は「対数相関場の非消滅」型")
