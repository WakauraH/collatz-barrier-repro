"""exp9_ridge_ostrowski2.py — (i) δ_m: ridge プロファイル固定点と wild 境界層の実測。
(ii) Ostrowski 第2階層: 標準語行列再帰の厳密検証と導来語スペクトロスコピー。

(i) g-再帰 (exp5b) を再走して以下を記録:
    - プロファイル P_m(u) = |g_m(k*+u)|/δ_m, u ∈ [-8,8] の m 収束 (L-δ3 の固定点仮説)
    - wild 境界層 w_m(r) = |g_m(r)|, r ∈ [-10, 2] の減衰率 (相殺解析の境界データ)

(ii) - σ 語 = 標準語再帰 s_{n+1} = s_n^{a_{n+1}} s_{n-1} (s0="0", s1="1", CF digits) の検証
     - 転送行列 B_n = M(s_n) の再帰 B_{n+1} = B_n^{a} B_{n-1} を mod p で厳密検証
       (打ち切り D、ブロック長 L の範囲で左上 (D-L) 角は厳密)
     - c(k) = e0 · M(σ_1)···M(σ_{k-1}) · 1 の検証 (mod p)
     - 導来語階層 (レベル1..4) への Δφ 分散分解 (R² ラダー) — 残差18%の解明
"""
import cmath
import math
from decimal import Decimal, getcontext

import numpy as np

from exp8_renorm_ostrowski import stable_log2c, H, THETA

getcontext().prec = 60
AMAX = 64
KLO = -96


# ---------- (i) ----------
def ridge_data(M_TOP=48):
    KHI = int(1.75 * M_TOP) + 20
    ks = list(range(KLO, KHI + 1))
    g_prev = {k: 1.0 + 0j for k in ks}
    weights = [2.0 ** -a for a in range(1, AMAX + 1)]
    out = {}
    for m in range(1, M_TOP + 1):
        M3 = 3 ** m
        inv2 = pow(2, -1, M3)
        pw = {}
        v = pow(inv2, -(KLO - AMAX), M3)
        pw[KLO - AMAX] = v
        for j in range(KLO - AMAX + 1, KHI + 1):
            v = (v * 2) % M3
            pw[j] = v
        g_cur = {}
        for k in ks:
            s = 0j
            for a in range(1, AMAX + 1):
                ka = k - a
                if ka < KLO:
                    break
                s += weights[a - 1] * cmath.exp(2j * math.pi * pw[ka] / M3) * g_prev[ka]
            g_cur[k] = s
        g_prev = g_cur
        kstar = max((k for k in ks if k >= 0), key=lambda k: abs(g_cur[k]))
        out[m] = (kstar, {u: abs(g_cur[kstar + u]) for u in range(-8, 9)},
                  {r: abs(g_cur[r]) for r in range(-10, 3)})
    return out


# ---------- (ii) ----------
def cf_digits_theta(n=12):
    x = Decimal(2).ln() / Decimal(3).ln()  # theta = log_3 2 = [0; a1, a2, ...]
    digits = []
    x = 1 / x
    for _ in range(n):
        a = int(x)
        digits.append(a)
        x = 1 / (x - a)
    return digits  # [a1, a2, ...] = [1,1,1,2,2,3,1,5,...]


def letter_matrices(D, p):
    U = np.zeros((D, D), dtype=np.int64)   # sigma=0: d->d, d->d+1
    T = np.zeros((D, D), dtype=np.int64)   # sigma=1: d->d, d->d-1
    for d in range(D):
        U[d][d] = 1
        if d + 1 < D:
            U[d][d + 1] = 1
        T[d][d] = 1
        if d - 1 >= 0:
            T[d][d - 1] = 1
    return U % p, T % p


def word_matrix(word, U, T, p):
    Mt = np.eye(U.shape[0], dtype=np.int64)
    for ch in word:
        Mt = (Mt @ (T if ch == 1 else U)) % p
    return Mt


def parse_blocks(seq, isolated):
    """isolated 文字で始まるブロック (isolated, run of other) に分割。
    返り値: (blocks: list of (start, length, run_length), 先頭の不完全部を除外)"""
    blocks = []
    i = 0
    n = len(seq)
    while i < n and seq[i] != isolated:
        i += 1
    while i < n:
        j = i + 1
        while j < n and seq[j] != isolated:
            j += 1
        if j >= n:
            break
        blocks.append((i, j - i, j - i - 1))  # run_length = ブロック長-1
        i = j
    return blocks


if __name__ == "__main__":
    print("=== (i) ridge プロファイルと wild 境界層 ===")
    data = ridge_data(48)
    print("プロファイル P_m(u) (u=-4..4), m = 24, 36, 48:")
    for m in (24, 36, 48):
        kstar, prof, wild = data[m]
        row = "  ".join(f"{prof[u]/prof[0]:.3f}" for u in range(-4, 5))
        print(f"  m={m}: k*={kstar}  [{row}]")
    print("wild 境界層の減衰率 log2 w_m(r)/m (m=48) と δ_m 率 -0.0850 の比較:")
    for r in (-1, -3, -6, -10):
        w48 = data[48][2][r]
        w24 = data[24][2][r]
        rate = (math.log2(w48) - math.log2(w24)) / 24
        print(f"  r={r:3d}: w_48={w48:.3e}  増分率(24→48) = {rate:+.4f}")

    print("\n=== (ii) Ostrowski 第2階層 ===")
    K = 30000
    logs, sigmas = stable_log2c(K)
    sig = list(sigmas[1:])  # σ_1, σ_2, ... (index 0 = σ_1)

    # 標準語再帰の検証
    a = cf_digits_theta(12)
    print(f"CF(log₃2) digits: {a}")
    s_prev, s_cur = [0], [1]
    qs = [1, 1]
    words = [s_prev, s_cur]
    for i in range(1, 9):
        s_next = s_cur * a[i] + s_prev
        s_prev, s_cur = s_cur, s_next
        words.append(s_cur)
        qs.append(len(s_cur))
    print(f"標準語長 (=収束分母): {qs}")
    ok = all(words[-1][:n] == sig[:n] for n in (100, 1000, len(words[-1])))
    print(f"σ 語 = lim s_n の検証 (長さ {len(words[-1])} まで): {'OK' if ok else 'NG'}")

    # 行列再帰 B_{n+1} = B_n^{a_{n+1}} B_{n-1} (mod p, 打ち切り厳密角)
    p = 3_000_017
    D = 700
    U, T = letter_matrices(D, p)
    Bs = [word_matrix(w, U, T, p) for w in words[:8]]  # q<=190 程度まで
    for n in range(1, 7):
        lhs = Bs[n + 1]
        rhs = np.eye(D, dtype=np.int64)
        for _ in range(a[n]):
            rhs = (rhs @ Bs[n]) % p
        rhs = (rhs @ Bs[n - 1]) % p
        L = len(words[n + 1])
        corner = D - L - 2
        assert np.array_equal(lhs[:corner, :corner], rhs[:corner, :corner]), n
    print(f"行列再帰 B_(n+1) = B_n^a · B_(n-1): n<=6 (q<= {len(words[7])}) で厳密一致 (mod {p})")

    # c(k) の行列表示検証
    from certtree import climbing_counts_dp
    c_exact = climbing_counts_dp(200)
    v = np.zeros(D, dtype=np.int64)
    v[0] = 1
    for k in (50, 100, 200):
        vv = v.copy()
        for j in range(k - 1):
            Mt = T if sig[j] == 1 else U
            vv = (vv @ Mt) % p
        assert int(vv.sum() % p) == c_exact[k] % p, k
    print("c(k) = e0·M(σ_1)···M(σ_(k-1))·1 の検証 (k=50,100,200, mod p): OK")

    # 導来語スペクトロスコピー: R² ラダー
    phi = logs[1:K + 1] - H * np.arange(1, K + 1)
    dphi = np.diff(phi)
    N = len(dphi)

    def r2_of_contexts(ctx):
        groups = {}
        for i in range(N):
            groups.setdefault(ctx[i], []).append(dphi[i])
        pred = np.empty(N)
        means = {g: float(np.mean(vs)) for g, vs in groups.items()}
        for i in range(N):
            pred[i] = means[ctx[i]]
        ss_res = float(((dphi - pred) ** 2).sum())
        ss_tot = float(((dphi - dphi.mean()) ** 2).sum())
        return 1 - ss_res / ss_tot, len(groups)

    # レベル1: 文字
    ctx1 = [("L1", sig[i]) for i in range(N)]
    # レベル2..4: 再帰的ブロック分割 (0 が孤立 → "0 1^r" ブロック)
    level_seq = sig[:N]
    ctx = [None] * N
    pos_map = list(range(N))  # 現レベル要素 -> 元位置の代表(開始位置)
    elem_span = [[i] for i in range(N)]  # 各要素が覆う元位置
    r2s = []
    r2, ng = r2_of_contexts(ctx1)
    r2s.append((1, r2, ng))
    cur_seq = level_seq
    cur_span = elem_span
    for lvl in (2, 3, 4):
        vals = sorted(set(cur_seq))
        # 孤立している方の文字を検出
        iso = None
        for cand in vals:
            idxs = [i for i, x in enumerate(cur_seq[:4000]) if x == cand]
            if all(b - a_ >= 2 for a_, b in zip(idxs, idxs[1:])):
                iso = cand
                break
        if iso is None:
            break
        blocks = parse_blocks(cur_seq, iso)
        new_seq, new_span, ctx_lvl = [], [], [None] * N
        for (st, ln, r_) in blocks:
            span = [pp for e in range(st, st + ln) for pp in cur_span[e]]
            new_seq.append(r_)
            new_span.append(span)
            for off, pp in enumerate(span):
                ctx_lvl[pp] = (r_, off)
        cov = [c_ is not None for c_ in ctx_lvl]
        ctxL = [(ctx_lvl[i] if ctx_lvl[i] is not None else ("edge", i % 7)) for i in range(N)]
        r2, ng = r2_of_contexts(ctxL)
        r2s.append((lvl, r2, ng))
        cur_seq, cur_span = new_seq, new_span
    print("\nΔφ の導来語階層 R² ラダー (残差18%の分解):")
    for lvl, r2, ng in r2s:
        print(f"  レベル {lvl}: R² = {r2:.4f}  (文脈数 {ng})")
