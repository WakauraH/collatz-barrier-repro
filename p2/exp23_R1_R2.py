"""exp23_R1_R2.py — (R1)(R2) の実行。

(R1) 補題R1a (証明済み・本コードは検証): 行 j の黒集合 {e : |signed(3^{2j−2}2^e mod 3^m)|
  ≤ ε3^m} は 2倍鎖に分解される (|v| ≤ 3^m/4 なら v(e+1) = 2v(e) が厳密)。
  主鎖 = 文字通りの整数 3^{2j−2}2^e < ε3^m (Tao の主三角形)。
  仮説 NR: 走行窓内の異種種数 (主鎖以外の奇数種) は行あたり O(1)。
  → 本コードで (m,k) の帯別・行別に異種種数を全数計測し NR を検証する。

(R2) capped ℓ¹ 汎関数の帳簿監査: μ = −0.16, cap 深さ U₀ = 0.05m として
  N(m) := Σ_k 2^{μ·max(u,−U₀)}|g_m(k)| を格子データで計算し、一段不等式
    N(m) ≤ F(μ)·N(m−1) + S(m)
  (S(m) = flat/seam 注入項の実測) を全レベル m ≤ 400 で監査、S の大きさを記録。
"""
import math

import numpy as np

LOG2_3 = math.log2(3)
AMAX = 60
KLO = -96
EPS = 0.01


# ---------------- (R1) ----------------
def chain_scan(m, k, js):
    """各行 j: 走行窓 e ∈ [k−5j−80, k−2j+10] の黒位置を鎖に分解し
    (主鎖数, 異種鎖数, 黒点数) を返す。"""
    M3 = 3 ** m
    inv2 = pow(2, -1, M3)
    thr = int(EPS * M3)
    out = []
    for j in js:
        p3 = pow(3, 2 * j - 2, M3)
        e_lo, e_hi = k - 5 * j - 80, k - 2 * j + 10
        v = (p3 * (pow(2, e_lo, M3) if e_lo >= 0 else pow(inv2, -e_lo, M3))) % M3
        blacks = []
        e = e_lo
        while e <= e_hi:
            sv = v if v <= M3 // 2 else v - M3
            if abs(sv) <= thr:
                blacks.append((e, sv))
            v = (2 * v) % M3
            e += 1
        # 鎖分解: 奇数部で分類
        seeds = {}
        for e, sv in blacks:
            w = abs(sv)
            if w == 0:
                continue
            while w % 2 == 0:
                w //= 2
            seeds.setdefault(w, []).append(e)
        primary = 0
        exotic = 0
        for w, es in seeds.items():
            # 主鎖判定: 文字通りの整数 3^{2j−2}·2^e (< M3) の奇数部は 3^{2j−2}
            if w == p3 % M3 and p3 < M3:
                primary += 1
            elif pow(3, 2 * j - 2, 10 ** 30) == w:  # 小さい場合の別表現
                primary += 1
            else:
                exotic += 1
        out.append((j, primary, exotic, len(blacks)))
    return out


# ---------------- (R2) ----------------
def audit_R2(M_TOP=400, mu=-0.16, cap_frac=0.05):
    KHI = int(1.9 * M_TOP) + 40
    W = KHI - KLO + 1
    g = np.ones(W, dtype=np.complex128)
    wts = np.array([2.0 ** -a for a in range(1, AMAX + 1)])
    ks = np.arange(KLO, KHI + 1, dtype=float)
    F_mu = 3.0 ** (-mu) / (2.0 ** (1 - mu) - 1)
    logscale = 0.0
    prevN = None
    viol = 0
    Smax_rel = 0.0
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
        U0 = cap_frac * m
        wcap = np.exp2(mu * np.maximum(u, -U0))
        N = float((wcap * mags).sum())
        l2N = logscale + math.log2(N)
        if prevN is not None:
            # S(m) := N(m) − F(μ)N(m−1)  (負なら不等式は S なしで成立)
            S_rel = (2.0 ** (l2N) - F_mu * 2.0 ** prevN) / 2.0 ** l2N
            if S_rel > 0:
                viol += 1
                Smax_rel = max(Smax_rel, S_rel)
        prevN = l2N
        s = mags.max()
        g /= s
        logscale += math.log2(s)
    return viol, Smax_rel, F_mu


if __name__ == "__main__":
    print("=== (R1) NR 仮説の全数検証 (異種種数の計測) ===")
    m = 240
    for tag, k in [("deep k=0.2mα", int(0.2 * m * LOG2_3)),
                   ("mid  k=0.5mα", int(0.5 * m * LOG2_3)),
                   ("shoulder δ=0.05", int(m * LOG2_3 - 0.05 * m)),
                   ("ridge", int(m * LOG2_3 - 7))]:
        js = list(range(2, m // 2, 7))
        res = chain_scan(m, k, js)
        tot_p = sum(r[1] for r in res)
        tot_x = sum(r[2] for r in res)
        max_x = max(r[2] for r in res)
        rows = len(res)
        print(f"  {tag:18s}: 行数={rows}  主鎖計={tot_p}  異種鎖計={tot_x} "
              f"(行平均 {tot_x/rows:.2f}, 行最大 {max_x})")
    print("  NR 判定: 異種鎖が行あたり O(1) に留まるか\n")

    print("=== (R2) capped 汎関数の一段不等式監査 (μ=−0.16, U₀=0.05m) ===")
    viol, Smax, F_mu = audit_R2()
    print(f"  F(μ) = {F_mu:.6f} (= 2^{{-{-math.log2(F_mu):.4f}}})")
    print(f"  N(m) ≤ F(μ)N(m−1) の破れ: {viol}/399 レベル, 最大相対注入 S/N = {Smax:.3e}")
    print("  (S/N が小さく破れが有界なら、帳簿は注入項付きで閉じる)")
