"""exp18_l4_contraction.py — 4重連鎖の臨界線計算の検証。

(1) 解析: 4因子(独立 a-歩み × 共通周波数)の位相なし重み付き行和は因子分解し
    F4(λ) = [3^{−λ}/(2^{1−λ}−1)]⁴, min_λ F4 = (2^{−I₀})⁴ = 2^{−4I₀}
    を高精度確認 (サイクル1の Legendre 最適の座標ごと適用)。
(2) ブリッジ (m ≤ 13): 窓内 ℓ⁴ 質量 S4_win = Σ_{k∈窓}|g_m(k)|⁴ が
    全周波数 S4'(FFT) をどれだけ捕捉するか。
(3) 大 m (≤ 400): S4_win の per-level 減衰率が 4I₀ = 0.317274 bits へ
    収束するか、Q_win = S4_win/δ⁴ が飽和するか。
"""
import math
from decimal import Decimal, getcontext

import numpy as np

getcontext().prec = 50
AMAX = 60
KLO = -96
I0 = 0.0793186127748554


def part1():
    ln2, ln3 = Decimal(2).ln(), Decimal(3).ln()
    L = ln3 / ln2
    # F(λ) = 3^{−λ}/(2^{1−λ}−1); 最適 2^{1−λ†} = L/(L−1) ⇒ λ† = 1 − log2(L/(L−1))
    lam = 1 - ((L / (L - 1)).ln() / ln2)
    F = (-lam * ln3).exp() / (Decimal(2) ** (1 - lam) - 1)
    lhs = -(F.ln() / ln2) * 4
    theta = ln2 / ln3
    H = -(theta * (theta.ln() / ln2) + (1 - theta) * ((1 - theta).ln() / ln2))
    rhs = 4 * (1 - H) / theta
    print(f"  λ† = {float(lam):+.10f}  (= −λ*)")
    print(f"  −log₂ F(λ†)⁴ = {float(lhs):.12f}")
    print(f"  4·I₀        = {float(rhs):.12f}")
    print(f"  差 = {float(abs(lhs - rhs)):.2e}  (恒等式 ⇒ 4重連鎖の位相なし縮小率 = 2^(−4I₀))")
    assert abs(lhs - rhs) < Decimal(10) ** -40


def dist_pi(m):
    M = 3 ** m
    inv2 = pow(2, -1, M)
    w = 2.0 ** -(np.arange(1, AMAX + 1))
    w /= w.sum()
    p = np.zeros(M)
    p[0] = 1.0
    idx = np.arange(M, dtype=np.int64)
    base = (3 * idx + 1) % M
    for _ in range(m):
        q = np.zeros(M)
        cur = base.copy()
        for a in range(AMAX):
            cur = (cur * inv2) % M
            q += w[a] * np.bincount(cur, weights=p, minlength=M)
        p = q
    return p


def lattice_S4(M_TOP, KHI_factor=1.9):
    KHI = int(KHI_factor * M_TOP) + 40
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
        s = mags.max()
        # 絶対スケール: log2 S4_win = 4·logscale + log2 Σ (mags/s ... 正規化前に加算)
        S4_rel = float((mags ** 4).sum())
        out[m] = (4 * logscale + math.log2(S4_rel),
                  logscale + math.log2(s))  # (log2 S4_win, log2 δ_win)
        g /= s
        logscale += math.log2(s)
    return out


if __name__ == "__main__":
    print("=== (1) 4重連鎖の Legendre 恒等式 ===")
    part1()

    print("\n=== (2) ブリッジ検証 (m ≤ 13): S4_win vs S4'(全周波数 FFT) ===")
    lat_small = lattice_S4(13)
    for m in range(6, 14):
        p = dist_pi(m)
        F = np.abs(np.fft.fft(p))
        xi = np.arange(3 ** m)
        Fm = F[(xi % 3 != 0)]
        S4_full = float((Fm ** 4).sum())
        l2win = lat_small[m][0]
        cover = 2.0 ** l2win / S4_full
        print(f"  m={m:2d}: S4_win/S4' = {cover:.4f}")

    print("\n=== (3) 大 m: S4_win の減衰率 → 4I₀? ===")
    lat = lattice_S4(400)
    print("  m, log2 S4_win + 4I₀m, per-level rate (Δ20), Q_win = S4_win/δ⁴:")
    prev = None
    for m in (100, 150, 200, 250, 300, 350, 400):
        l2S4, l2d = lat[m]
        l2S4b, _ = lat[m - 20]
        rate = -(l2S4 - l2S4b) / 20
        Q = 2.0 ** (l2S4 - 4 * l2d)
        print(f"  m={m:3d}: {l2S4 + 4*I0*m:8.3f}   rate={rate:.5f}   Q_win={Q:7.2f}")
    print(f"  目標: rate → 4I₀ = {4*I0:.5f} (上から片側収束)、Q_win 飽和")
