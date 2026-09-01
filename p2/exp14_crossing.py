"""exp14_crossing.py — サイクル3実行: 横断和の構造解析 (E′)。

寄与行列 C(j,A) = amp_j(A) · F(m−j, k*−A),
  F(d,r) = Σ_{a>r} 2^{−a} e_{3^d}(2^{r−a}) · g_{d−1}(r−a)   (2冪周波数 ⇒ 格子で厳密),
  g_m(k*) = M_m + Σ C(j,A)   (恒等式検証付き)。

測定 (事前登録 S1–S3 / F1–F2):
  S1: 上位セル帯が |ΣC| の ≥70% を担い、帯中心 (j*/m, r* = k*−A*) が m で安定
  S2: 帯に沿う位相の2階差分が O(1/m)
  S3: 帯のみの部分和が g を振幅 20% 以内で再構成
"""
import cmath
import math

import numpy as np

AMAX = 64
KLO = -96
LOG2_3 = math.log2(3)
I0 = 0.0793186127748554


def lattice_store(M_TOP):
    KHI = int(1.66 * M_TOP) + 40
    W = KHI - KLO + 1
    g = np.ones(W, dtype=np.complex128)
    wts = np.array([2.0 ** -a for a in range(1, AMAX + 1)])
    store = {0: (g.copy(), 0.0)}
    logscale = 0.0
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
        s = mags.max()
        g /= s
        logscale += math.log2(s)
        store[m] = (g.copy(), logscale)
    return store, kstars, W


def g_abs(store, d, r):
    """絶対スケールの g_d(r) (r は指数; 窓外は 0)。"""
    arr, ls = store[d]
    i = r - KLO
    if i < 0 or i >= len(arr):
        return 0j
    return arr[i] * (2.0 ** ls)


def F_val(store, d, r):
    if d == 0:
        return 1.0 + 0j if r < 0 else sum(2.0 ** -a for a in range(r + 1, r + AMAX + 1)) + 0j
    M3 = 3 ** d
    inv2 = pow(2, -1, M3)
    s = 0j
    for a in range(max(r + 1, 1), r + AMAX + 1):
        e = a - r
        val = pow(inv2, e, M3)
        phase = cmath.exp(2j * math.pi * val / M3)
        s += 2.0 ** -a * phase * g_abs(store, d - 1, r - a)
    return s


def amp_dp(m, k):
    LN2, LN3 = math.log(2), math.log(3)
    amps = []
    amp = np.zeros(k + 1, dtype=np.complex128)
    amp[0] = 1.0
    amps.append(amp.copy())
    wts = np.array([2.0 ** -a for a in range(1, AMAX + 1)])
    A_idx = np.arange(k + 1, dtype=float)
    for j in range(1, m + 1):
        expo = (k - A_idx) * LN2 + (j - 1 - m) * LN3
        arg = np.where(expo > -42, np.exp(np.clip(expo, None, 5)), 0.0)
        phase = np.exp(2j * np.pi * arg)
        nxt = np.zeros(k + 1, dtype=np.complex128)
        for a in range(1, AMAX + 1):
            if a > k:
                break
            nxt[a:] += wts[a - 1] * amp[:-a] * phase[a:]
        amp = nxt
        amps.append(amp.copy())
    return amps


if __name__ == "__main__":
    M_TOP = 100
    store, kstars, W = lattice_store(M_TOP)
    print("m, 恒等式相対誤差, 上位セル(j/m, r=k*−A), 70%質量セル数/全セル, 帯部分和/|g|:")
    for m in (24, 32, 40, 48, 60, 80, 100):
        k = kstars[m]
        amps = amp_dp(m, k)
        # C(j, A)
        Cs = {}
        total = 0j
        for j in range(m):
            d = m - j
            for A in range(0, k + 1):
                c = amps[j][A]
                if abs(c) < 1e-30:
                    continue
                Fv = F_val(store, d, k - A)
                if Fv == 0:
                    continue
                val = c * Fv
                Cs[(j, A)] = val
                total += val
        Mterm = amps[m].sum()
        gval = g_abs(store, m, k)
        rel = abs((total + Mterm) - gval) / abs(gval)
        # 質量分布
        items = sorted(Cs.items(), key=lambda kv: -abs(kv[1]))
        Ssum = sum(abs(v) for _, v in Cs.items())
        acc, nsel, band = 0.0, 0, []
        for key, v in items:
            acc += abs(v)
            band.append(key)
            nsel += 1
            if acc >= 0.7 * Ssum:
                break
        (jtop, Atop) = items[0][0]
        band_sum = sum(Cs[key] for key in band)
        print(f"  m={m:3d}: 誤差={rel:.2e}  top=(j/m={jtop/m:.3f}, r={k-Atop:2d})  "
              f"70%帯={nsel}/{len(Cs)} ({100*nsel/len(Cs):.1f}%)  "
              f"|帯和|/|g|={abs(band_sum)/abs(gval):.3f}")
    # 帯中心の安定性と位相曲率 (m=60 で代表)
    m = 60
    k = kstars[m]
    amps = amp_dp(m, k)
    print("\nm=60 の |C| 質量の (j/m) 周辺分布と、r = k−A 分布:")
    massJ = np.zeros(m)
    massR = {}
    for j in range(m):
        d = m - j
        for A in range(0, k + 1):
            c = amps[j][A]
            if abs(c) < 1e-30:
                continue
            v = abs(c * F_val(store, d, k - A))
            massJ[j] += v
            massR[k - A] = massR.get(k - A, 0.0) + v
    top_j = np.argsort(massJ)[-5:][::-1]
    print(f"  j 質量上位5: {[(int(j), f'{j/m:.2f}') for j in top_j]}")
    rs = sorted(massR.items(), key=lambda kv: -kv[1])[:6]
    print(f"  r 質量上位6: {[(r, f'{v:.2e}') for r, v in rs]}")
