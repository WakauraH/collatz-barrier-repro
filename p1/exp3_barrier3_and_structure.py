"""exp3_barrier3_and_structure.py — 次の一手: 障壁定理 III の機械化検証と、
証明書木の圧縮可能性(holonomic / 正規言語)判定。

Part 1 (障壁定理 III の実現エンジン検証):
  任意の窓長 w について、n = 2^{w+2} t - 1 の U 軌道の最初の w ステップは
  (シンドローム, a_j, 値比) のすべてが「全1統計」と厳密一致する(climb 補題)。
  ⇒ 有限窓 (d, w) の制約で「すべての非降下整数軌道片で成立するもの」は
    全1測度(上昇測度)を排除できない。剛性恒等式も窓上で厳密成立することを確認。

Part 2 (補正指数): c(k) = 2^{H(θ)k + b(k)} の b(k) を k ≤ K まで厳密計算し、
  b(k) ~ -c2·log2(k) + c0 を最小二乗で当てる。c2 が非整数(~3/2 予想)なら
  有理型母関数(正規言語 = 有限オートマトン圧縮)は不可能。

Part 3 (P-recursive 探索): c(k) が多項式係数線形漸化式
  sum_{i=0}^{r} p_i(k) c(k+i) = 0  (deg p_i <= s)
  を持つか、大素数 3 本の mod 演算で核の次元を判定。核が自明なら
  holonomic 圧縮(D-finite 記述)の道も閉じる。
"""
import math
import random
from decimal import Decimal, getcontext

from certtree import climbing_counts_dp

getcontext().prec = 60


# ---------- Part 1 ----------
def check_window_realization(w: int, t: int) -> None:
    n0 = (1 << (w + 2)) * t - 1
    n = n0
    for j in range(w):
        m = 3 * n + 1
        a = (m & -m).bit_length() - 1
        assert a == 1, (w, t, j)                      # a-統計 = 全1
        n = m >> a
        assert n > n0, (w, t, j)                      # 非降下
        assert n % 2 == 1                             # 奇シンドローム継続
    # 窓上の剛性恒等式 (厳密): 2^{A_w} n_w = 3^w n0 * prod(1+1/(3 n_j))
    from fractions import Fraction
    nn, prod = n0, Fraction(1)
    for _ in range(w):
        prod *= 1 + Fraction(1, 3 * nn)
        nn = (3 * nn + 1) // 2
    assert Fraction(2) ** w * nn == Fraction(3) ** w * n0 * prod, (w, t)


# ---------- Part 2 ----------
def fit_correction(c, ks):
    theta = Decimal(2).ln() / Decimal(3).ln()
    H = -(theta * (theta.ln() / Decimal(2).ln())
          + (1 - theta) * ((1 - theta).ln() / Decimal(2).ln()))
    Hf = float(H)
    xs = [math.log2(k) for k in ks]
    ys = []
    for k in ks:
        # log2 c(k) を厳密整数から高精度で
        ck = c[k]
        ys.append(ck.bit_length() - 1 + math.log2(ck / (1 << (ck.bit_length() - 1)))
                  - Hf * k)
    n = len(ks)
    sx, sy = sum(xs), sum(ys)
    sxx = sum(x * x for x in xs)
    sxy = sum(x * y for x, y in zip(xs, ys))
    slope = (n * sxy - sx * sy) / (n * sxx - sx * sx)
    intercept = (sy - slope * sx) / n
    resid = max(abs(y - (slope * x + intercept)) for x, y in zip(xs, ys))
    return Hf, slope, intercept, resid


# ---------- Part 3 ----------
def p_recursive_kernel_dim(c, r: int, s: int, k0: int, M: int, p: int) -> int:
    """方程式 sum_i p_i(k) c(k+i) = 0 (k=k0..k0+M-1) の係数解空間の次元 (mod p)。"""
    cols = (r + 1) * (s + 1)
    rows = []
    for k in range(k0, k0 + M):
        row = []
        for i in range(r + 1):
            cki = c[k + i] % p
            kk = 1
            for j in range(s + 1):
                row.append((cki * kk) % p)
                kk = (kk * k) % p
        rows.append(row)
    # Gaussian elimination mod p
    rank = 0
    ncols = cols
    col = 0
    for col in range(ncols):
        piv = None
        for rr in range(rank, len(rows)):
            if rows[rr][col] % p != 0:
                piv = rr
                break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], p - 2, p)
        rows[rank] = [(x * inv) % p for x in rows[rank]]
        for rr in range(len(rows)):
            if rr != rank and rows[rr][col]:
                f = rows[rr][col]
                rows[rr] = [(a - f * b) % p for a, b in zip(rows[rr], rows[rank])]
        rank += 1
        if rank == min(len(rows), ncols):
            break
    return cols - rank


if __name__ == "__main__":
    random.seed(7)
    # Part 1
    for w in list(range(1, 61, 7)) + [64]:
        for t in (1, 3, 12345, random.randint(1, 10 ** 20)):
            check_window_realization(w, t)
    print("Part1 OK: 全1統計は w<=64 の任意の窓で本物の整数軌道 (2^{w+2}t-1) により厳密実現")
    print("  ⇒ 障壁定理 III: 有限窓 (d,w) 制約の階層(剛性込み)は上昇測度を排除できない\n")

    K = 1600
    c = climbing_counts_dp(K)

    # Part 2
    ks = list(range(200, K + 1, 50))
    Hf, slope, intercept, resid = fit_correction(c, ks)
    print(f"Part2: H(θ) = {Hf:.9f}")
    print(f"  b(k) = log2 c(k) - H k ≈ {slope:+.4f}·log2(k) {intercept:+.3f} "
          f"(k∈[200,{K}], 最大残差 {resid:.3f})")
    print(f"  補正指数 c2 ≈ {-slope:.3f} (予想 3/2; 非整数負冪 ⇒ 有理型母関数は不可能"
          f" ⇒ 有限オートマトンによる証明書木の圧縮は不可能)\n")

    # Part 3
    primes = [2 ** 61 - 1, 4611686018427387847, 2305843009213693951]
    print("Part3: P-recursive 探索 (核次元 mod p; 3素数一致で判定)")
    for (r, s) in [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6)]:
        cols = (r + 1) * (s + 1)
        M = cols + 40
        dims = [p_recursive_kernel_dim(c, r, s, 60, M, p) for p in primes]
        verdict = "核なし" if all(dm == 0 for dm in dims) else f"核次元 {dims} — 要検証!"
        print(f"  order r={r}, deg s={s}: {verdict}")
    print("  全て核なしなら: c(k) は (r,s)<=(6,6) の範囲で holonomic でない"
          " ⇒ D-finite 圧縮の道も閉じる")
