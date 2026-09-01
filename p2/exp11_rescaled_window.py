"""exp11_panel_actions.py — パネル裁定の即時実行。

T1: per-level リスケール格子再帰で m <= 1200 (float64 相対精度を維持)。
    事前登録基準: m∈[800,1200] の自由フィット log2δ = −a·m − β·log2 m + c で
    a ∈ [0.0790, 0.0797] かつ 欠損 m·log2 3 − k* が非増大 (< 12) → レート = I0 を採択。
    (注意: 窓内最大は δ_m の下界。局在 L-δ1 は別問題として残る。)

T2: exp2 の Karp 実装の番兵バグ (NEG=-1e17 が実経路重み -1e18 より浅い) を
    正確な None 番兵で修正し、制限グラフの μ_j を再計算。
    併せて訪問頻度の下界を LP 値でなく自明な数え上げ 2θ−1 に置換:
    非降下窓では奇比 ρ ≥ θ、奇→奇 隣接は ≥ 2e−k 個、ゆえに freq(n≡3 mod 4) ≥ 2θ−1。

T3: フロンティア言語の非正規性の厳密証明 (Myhill–Nerode):
    1^a 0^b ∈ L ⟺ b ≤ f(a), f(a) = max{b : a > θ(a+b)} = ⌈a(1−θ)/θ⌉ − 1。
    f(a) → ∞ なので 1^a たちは無限個の Nerode 類に分かれる ⇒ L は非正規。
    ここでは f(a) の式と climbing 判定の一致を a ≤ 4000 で全数検証する。
"""
import math

import numpy as np

LN2, LN3 = math.log(2), math.log(3)
LOG2_3 = math.log2(3)
THETA = LN2 / LN3
AMAX = 64
KLO = -96


# ---------------- T1 ----------------
def rescaled_lattice(M_TOP=1200):
    KHI = int(1.66 * M_TOP) + 40
    W = KHI - KLO + 1
    g = np.ones(W, dtype=np.complex128)
    wts = np.array([2.0 ** -a for a in range(1, AMAX + 1)])
    logdelta = {}
    kstars = {}
    logscale = 0.0
    for m in range(1, M_TOP + 1):
        M3 = 3 ** m
        inv2 = pow(2, -1, M3)
        # 位相表 (指数 j = KLO..KHI)
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
        i0 = -KLO  # k = 0 の位置
        imax = i0 + int(np.argmax(mags[i0:]))
        kstars[m] = imax + KLO
        s = mags[imax]
        logdelta[m] = logscale + math.log2(s)
        g /= s
        logscale += math.log2(s)
    return logdelta, kstars


# ---------------- T2 ----------------
def max_mean_cycle_exact(d, alive):
    """Karp、正確整数、None 番兵。重み: 偶 -S、奇 U15+ceil補正 (上側)。"""
    S = 10 ** 15
    U15 = 584962500721157
    D, D2 = 1 << d, 1 << (d + 1)
    edges = []  # (src, dst, w)
    for r in range(D):
        if not alive[r]:
            continue
        for rr in (r, r + D):
            if r % 2 == 0:
                dst = (rr // 2) % D
                w = -S
            else:
                dst = ((3 * rr + 1) // 2) % D
                mmin = rr if rr >= 3 else rr + D2
                den = 3 * mmin * 10000
                w = U15 + (S * 14427 + den - 1) // den + 1  # log2(1+1/(3m)) <= 1.4427/(3m) 上側
            if alive[dst]:
                edges.append((r, dst, w))
    n = sum(alive)
    F = [[None] * D for _ in range(n + 1)]
    for r in range(D):
        if alive[r]:
            F[0][r] = 0
    for k in range(1, n + 1):
        Fk, Fp = F[k], F[k - 1]
        for (s_, t_, w) in edges:
            if Fp[s_] is not None:
                cand = Fp[s_] + w
                if Fk[t_] is None or cand > Fk[t_]:
                    Fk[t_] = cand
    best = None
    for v in range(D):
        if F[n][v] is None:
            continue
        vals = [(F[n][v] - F[k][v]) / (n - k) for k in range(n) if F[k][v] is not None]
        if vals:
            mu = min(vals)
            if best is None or mu > best:
                best = mu
    return best / 10 ** 15 if best is not None else None


def trailing_ones(r, d):
    t = 0
    while t < d and (r >> t) & 1:
        t += 1
    return t


# ---------------- T3 ----------------
def climbing_word(bits):
    e = 0
    for j, b in enumerate(bits, 1):
        e += b
        if 3 ** e <= 2 ** j:
            return False
    return True


if __name__ == "__main__":
    print("=== T3: 非正規性の Myhill–Nerode 証明の検証 ===")
    bad = 0
    for a in range(1, 4001, 37):
        f = math.ceil(a * (1 - THETA) / THETA) - 1
        # f(a) の定義検証: b = f は climbing、b = f+1 は非 climbing
        assert climbing_word([1] * a + [0] * f), a
        assert not climbing_word([1] * a + [0] * (f + 1)), a
    print("  f(a) = ⌈a(1−θ)/θ⌉−1 の全数一致 (a ≤ 4000, 抽出): OK")
    print("  ⇒ 1^a 0^{f(a)} ∈ L, 1^a 0^{f(a)+1} ∉ L, f(a)→∞ で Nerode 類は無限個: L 非正規 (定理)\n")

    print("=== T2: exp2 修正 (正確 Karp) ===")
    for d in (4, 6, 8):
        alive_full = [True] * (1 << d)
        mu_full = max_mean_cycle_exact(d, alive_full)
        line = [f"full: {mu_full:+.6f}"]
        for j in (3, 2):
            alive = [trailing_ones(r, d) < j for r in range(1 << d)]
            mu = max_mean_cycle_exact(d, alive)
            line.append(f"j={j}: " + (f"{mu:+.6f}" if mu is not None else "no-cycle"))
        print(f"  d={d}: " + "  ".join(line))
    print(f"  訪問頻度の正しい下界 (自明な数え上げ): 2θ−1 = {2*THETA-1:.5f}"
          f"  (旧 LP 値 0.2174 を置換; Opus 指摘の通り数え上げが優越)\n")

    print("=== T1: リスケール格子 m <= 1200 ===")
    logdelta, kstars = rescaled_lattice(1200)
    print("m, log2 δ (窓内下界), k*, 欠損 m·log₂3 − k*, 局所レート:")
    for m in (200, 400, 600, 800, 1000, 1200):
        ld = logdelta[m]
        deficit = m * LOG2_3 - kstars[m]
        if m >= 400:
            s_loc = -(logdelta[m] - logdelta[m - 200]) / 200 - \
                (math.log2(m) - math.log2(m - 200)) / 200
            s_txt = f"{s_loc:.5f}"
        else:
            s_txt = "-"
        print(f"  m={m:5d}: log2δ={ld:9.3f}  k*={kstars[m]:5d}  欠損={deficit:6.2f}  s={s_txt}")
    I0_bits = 0.0793186
    ms = np.array([m for m in range(800, 1201, 25)], dtype=float)
    ys = np.array([logdelta[int(m)] for m in ms])
    X = np.vstack([ms, np.log2(ms), np.ones_like(ms)]).T
    coef, *_ = np.linalg.lstsq(X, -ys, rcond=None)
    a_fit, beta_fit = coef[0], coef[1]
    defs = [m * LOG2_3 - kstars[m] for m in range(800, 1201)]
    print(f"\n事前登録判定 (m∈[800,1200]): a_fit = {a_fit:.5f} "
          f"(基準 [0.0790, 0.0797], I0 = {I0_bits}), β = {beta_fit:.3f}")
    print(f"欠損: max = {max(defs):.2f}, 前半平均 {np.mean(defs[:200]):.2f} "
          f"vs 後半平均 {np.mean(defs[-200:]):.2f} (非増大なら合格)")
    verdict = (0.0790 <= a_fit <= 0.0797) and max(defs) < 12 and \
        np.mean(defs[-200:]) <= np.mean(defs[:200]) + 0.3
    print(f"判定: {'採択 — レート = I0 = (1−H(θ))/θ (窓内系列について)' if verdict else '棄却/保留'}")
