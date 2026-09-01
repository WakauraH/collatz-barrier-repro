"""exp17_Lalpha_Lbeta.py — 残補題 (Lα)(Lβ) への攻撃。

Part A ((Lα) ℓ⁴ 法): 全周波数厳密 (m ≤ 13) で S4'(m) = Σ_{3∤ξ}|f|⁴ と δ_m を計算。
  Q(m) = S4'/δ⁴ が poly(m) なら第4モーメントはリッジに集中し、
  sup ≤ (S4')^{1/4} = δ·Q^{1/4} の還元が有効 — (Lα) は S4' ≤ poly·2^{−4I₀m}
  というスカラー評価(4重積連鎖への重み付き縮小法の対象)に帰着する。
  対照: generic 床の寄与 ~ 2·3^{m}·(R_m/3^m)² = O(m²·3^{−m}) ≪ 2^{−4I₀m}。

Part B ((Lα) wrap 直接プロファイル): 窓 KHI = 2.6m の格子 (上方は厳密) で
  sup_{u∈[a,b]} |g_m(k)| / δ_m^{window} を u 帯ごとに測る (m = 100, 200)。
  単調減衰でリッジ近傍が sup なら (Lα) は線の O(1) 近傍に局在。

Part C ((Lβ) オクターブ因子): m = 640 で κ(s) = K(2s)/K(s) の s 依存を確認。
"""
import math

import numpy as np

AMAX = 60
KLO = -96
LN2, LN3 = math.log(2), math.log(3)
LOG2_3 = math.log2(3)
I0 = 0.0793186127748554


# ---------- Part A ----------
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


def part_A():
    print("m, δ_m, S4', Q = S4'/δ⁴, log2 S4' + 4·I0·m")
    for m in range(4, 14):
        p = dist_pi(m)
        F = np.abs(np.fft.fft(p))
        xi = np.arange(3 ** m)
        mask = (xi % 3 != 0)
        Fm = F[mask]
        delta = Fm.max()
        S4 = float((Fm ** 4).sum())
        Q = S4 / delta ** 4
        print(f"  m={m:2d}: δ={delta:.5e}  S4'={S4:.5e}  Q={Q:9.2f}  "
              f"log2S4'+4I0m={math.log2(S4) + 4*I0*m:7.3f}")


# ---------- Part B ----------
def part_B():
    for M_TOP in (100, 200):
        KHI = int(2.6 * M_TOP) + 40
        W = KHI - KLO + 1
        g = np.ones(W, dtype=np.complex128)
        wts = np.array([2.0 ** -a for a in range(1, AMAX + 1)])
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
            g /= np.abs(g).max()
        m = M_TOP
        mags = np.abs(g)
        ks = np.arange(KLO, KHI + 1, dtype=float)
        u = ks - m * LOG2_3
        ridge = mags[(u > -30) & (u <= 0)].max()
        print(f"  m={m}: 帯別 sup|g|/ridge (u = k − m·log₂3):")
        for (a, b) in [(0, 2), (2, 5), (5, 10), (10, 20), (20, 40), (40, 80),
                       (80, 160), (160, 260)]:
            sel = (u > a) & (u <= b) & (ks >= 0)
            if sel.any():
                r = mags[sel].max() / ridge
                print(f"    u∈({a:3d},{b:3d}]: {r:.4e}")


# ---------- Part C ----------
def lattice_kstar(M_TOP):
    KHI = int(1.66 * M_TOP) + 40
    W = KHI - KLO + 1
    g = np.ones(W, dtype=np.complex128)
    wts = np.array([2.0 ** -a for a in range(1, AMAX + 1)])
    kst = 0
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
        kst = i0x + int(np.argmax(mags[i0x:])) + KLO
        g /= mags.max()
    return kst


def hybrid_amp(m, k, s_active):
    J = m - 5
    amp = np.zeros(k + 1, dtype=np.complex128)
    amp[0] = 1.0
    wts = np.array([2.0 ** -a for a in range(1, AMAX + 1)])
    A_idx = np.arange(k + 1, dtype=float)
    for j in range(1, J + 1):
        if (J - j) < s_active:
            expo = (k - A_idx) * LN2 + (j - 1 - m) * LN3
            arg = np.where(expo > -42, np.exp(np.clip(expo, None, 5)), 0.0)
            phase = np.exp(2j * np.pi * arg)
            use_ph = True
        else:
            use_ph = False
        nxt = np.zeros(k + 1, dtype=np.complex128)
        for a in range(1, AMAX + 1):
            if a > k:
                break
            if use_ph:
                nxt[a:] += wts[a - 1] * amp[:-a] * phase[a:]
            else:
                nxt[a:] += wts[a - 1] * amp[:-a]
        amp = nxt
    return abs(amp[k])


def part_C():
    m = 640
    k = lattice_kstar(m)
    P = hybrid_amp(m, k, 0)
    prev = 1.0
    print(f"  m=640, k*={k}: オクターブ因子 κ(s) = K(2s)/K(s):")
    Ks = {}
    for s in (4, 8, 16, 32, 64, 128, 256, 512):
        Ks[s] = hybrid_amp(m, k, s) / P
    for s in (4, 8, 16, 32, 64, 128, 256):
        print(f"    s={s:4d}→{2*s:4d}: κ = {Ks[2*s]/Ks[s]:.4f}")


if __name__ == "__main__":
    print("=== Part A: (Lα) ℓ⁴ 法 ===")
    part_A()
    print("\n=== Part B: (Lα) wrap 域プロファイル ===")
    part_B()
    print("\n=== Part C: (Lβ) オクターブ因子 (m=640) ===")
    part_C()
