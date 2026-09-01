"""exp13_lower_bound.py — サイクル2実行: 振動的下界の構成 (S3 事前登録数値)。

k = k*(m) (格子 argmax) において
  主項  M_m = E[e(x Y_m); A_m ≤ k]   (位相自由領域の厳密期待値、複素 DP)
  越境項 W_m = g_m(k) − M_m           (検証済み繰り込み等式による分解)
を m ≤ 400 で分離計算し、事前登録判定:
  (S3a) log2|M_m| + I0·m の傾斜が |slope| < 0.005 bits/level → 主項がレートを担う
  (S3b) |W_m|/|M_m| が 1 に収束しない → 越境項は主指数まで打ち消さない (F2 不成立)
"""
import cmath
import math

import numpy as np

AMAX = 64
KLO = -96
LN2, LN3 = math.log(2), math.log(3)
LOG2_3 = math.log2(3)
I0 = 0.0793186127748554


def lattice_with_g(M_TOP=400):
    KHI = int(1.66 * M_TOP) + 40
    W = KHI - KLO + 1
    g = np.ones(W, dtype=np.complex128)
    wts = np.array([2.0 ** -a for a in range(1, AMAX + 1)])
    logscale = 0.0
    out = {}
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
        imax = i0x + int(np.argmax(mags[i0x:]))
        kstar = imax + KLO
        out[m] = (kstar, g[imax], logscale)  # g値は現スケール; 絶対 log2|g| = logscale + log2|g[imax]|
        s = mags[imax]
        g /= s
        logscale += math.log2(s)
    return out


def main_term(m, k):
    """M_m = E[e(x Y_m); A_m <= k] を複素 DP で厳密計算 (float)。"""
    amp = np.zeros(k + 1, dtype=np.complex128)
    amp[0] = 1.0
    wts = np.array([2.0 ** -a for a in range(1, AMAX + 1)])
    A_idx = np.arange(k + 1, dtype=float)
    for j in range(1, m + 1):
        # 位相: e(2π · 2^{k−A} · 3^{j−1−m}) を A ごとに
        expo = (k - A_idx) * LN2 + (j - 1 - m) * LN3
        arg = np.where(expo > -42, np.exp(np.clip(expo, None, 5)), 0.0)
        # arg > ~1 は位相自由領域を出る (A_m ≤ k の範囲では起きにくいが安全に許容)
        phase = np.exp(2j * np.pi * arg)
        nxt = np.zeros(k + 1, dtype=np.complex128)
        for a in range(1, AMAX + 1):
            if a > k:
                break
            nxt[a:] += wts[a - 1] * amp[:-a] * phase[a:]
        amp = nxt
    return amp.sum()


if __name__ == "__main__":
    print("格子 (g_m(k*) 記録付き) を構築中...")
    lat = lattice_with_g(400)
    print("m, k*, log2|M|+I0m, log2|g|+I0m, |W|/|M|:")
    rows = []
    for m in (60, 100, 150, 200, 250, 300, 350, 400):
        kstar, gval, logscale = lat[m]
        M = main_term(m, kstar)
        log2g = logscale + math.log2(abs(gval))
        # W = g − M: 絶対スケールで
        g_abs = gval * (2.0 ** 0)  # gval は logscale スケール済み: 実値 = gval·2^{logscale}
        # 比較は対数で: |W|/|M| = |g·2^{ls} − M|/|M|
        gfull = gval * (2.0 ** logscale) if logscale > -300 else None
        if gfull is not None:
            Wv = gfull - M
            ratio = abs(Wv) / abs(M) if abs(M) > 0 else float("inf")
        else:
            ratio = float("nan")
        l2M = math.log2(abs(M)) if abs(M) > 0 else float("-inf")
        rows.append((m, l2M + I0 * m, log2g + I0 * m, ratio))
        print(f"  m={m:3d}: k*={kstar:3d}  log2|M|+I0m={l2M + I0*m:8.3f}  "
              f"log2|g|+I0m={log2g + I0*m:8.3f}  |W|/|M|={ratio:.4f}")
    # S3a: 主項の傾斜 (m>=150)
    sel = [r for r in rows if r[0] >= 150]
    ms = np.array([r[0] for r in sel])
    ys = np.array([r[1] for r in sel])
    slope = np.polyfit(ms, ys, 1)[0]
    print(f"\nS3a: 主項 log2|M|+I0m の傾斜 = {slope:+.5f} bits/level "
          f"(|slope|<0.005 で合格)")
    rat_tail = [r[3] for r in sel]
    print(f"S3b: |W|/|M| (m>=150) = {['%.3f' % r for r in rat_tail]} "
          f"(→1 に収束しなければ F2 不成立)")
