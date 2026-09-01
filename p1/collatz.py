"""collatz.py — 基本写像・厳密恒等式・反例探索(Phase 3/5 の計算部分)。

写像の定義:
  T(n) = n/2 (n 偶数), 3n+1 (n 奇数)          — 問題文の T
  Tc(n) = n/2 (n 偶数), (3n+1)/2 (n 奇数)     — 圧縮版 (Terras)。T の奇数ステップ2回分。
  U(n) = (3n+1)/2^{v2(3n+1)}                  — 奇数→奇数の加速写像

すべて任意精度整数。実行すると自己検査 (assert) を全て走らせる。
"""
from fractions import Fraction


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def T(n: int) -> int:
    return n // 2 if n % 2 == 0 else 3 * n + 1


def Tc(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def U(n: int) -> int:
    assert n % 2 == 1
    m = 3 * n + 1
    return m >> v2(m)


def U_traj(n0: int, k: int):
    """奇数軌道 n_0..n_k と a_j = v2(3 n_j + 1) の列を返す。"""
    ns, As = [n0], []
    n = n0
    for _ in range(k):
        m = 3 * n + 1
        a = v2(m)
        n = m >> a
        ns.append(n)
        As.append(a)
    return ns, As


# ---------- Phase 3: 積表示 (厳密恒等式) ----------
def check_product_formula(n0: int, k: int) -> None:
    """n_k = (3^k n_0 + beta_k) / 2^{A_k},  beta_k = sum_{j=0}^{k-1} 3^{k-1-j} 2^{A_j}
    (A_0 = 0, A_j = a_0+...+a_{j-1}) を厳密検証。"""
    ns, As = U_traj(n0, k)
    Acum = [0]
    for a in As:
        Acum.append(Acum[-1] + a)
    beta = sum(3 ** (k - 1 - j) * 2 ** Acum[j] for j in range(k))
    assert ns[k] * 2 ** Acum[k] == 3 ** k * n0 + beta, (n0, k)


def check_rigidity(n0: int, k: int) -> None:
    """厳密な剛性恒等式: 2^{A_k} n_k = 3^k n_0 * prod_{j<k} (1 + 1/(3 n_j)) を有理数で検証。"""
    ns, As = U_traj(n0, k)
    A = sum(As)
    prod = Fraction(1)
    for j in range(k):
        prod *= 1 + Fraction(1, 3 * ns[j])
    assert Fraction(2) ** A * ns[k] == Fraction(3) ** k * n0 * prod, (n0, k)


# ---------- 障壁補題: n ≡ -1 (mod 2^m) は m-1 ステップ上昇 ----------
def check_minus_one_lemma(m: int, t: int) -> None:
    """n_j = 3^j 2^{m-j} t - 1 (j <= m-1), 各 a_j = 1 (j <= m-2), 単調増加。"""
    n0 = 2 ** m * t - 1
    ns, As = U_traj(n0, m - 1)
    for j in range(m):
        assert ns[j] == 3 ** j * 2 ** (m - j) * t - 1, (m, t, j)
    for j in range(m - 1):
        assert As[j] == 1, (m, t, j)
    for j in range(1, m):
        assert ns[j] > ns[j - 1] >= n0 or j == 1, (m, t, j)
        assert ns[j] > n0


# ---------- Terras 全単射: n mod 2^k ↦ 長さ k のパリティ列 は全単射 ----------
def parity_vector(n: int, k: int):
    v = []
    for _ in range(k):
        p = n & 1
        v.append(p)
        n = Tc(n) if p == 0 else (3 * n + 1) // 2
    return tuple(v)


def check_terras_bijection(k: int) -> None:
    seen = {parity_vector(r if r > 0 else 2 ** k, k) for r in range(2 ** k)}
    assert len(seen) == 2 ** k, k


# ---------- 反例探索: 小範囲全数収束 (L0 sanity) ----------
def verify_range(N: int) -> None:
    """すべての奇数 3 <= n <= N が自分未満へ降下することを検査 (強帰納法の有限部分)。"""
    for n in range(3, N + 1, 2):
        m = n
        while m >= n:
            m = U(m)
        # m < n に到達 → 強帰納法で 1 へ


if __name__ == "__main__":
    import random

    random.seed(12345)
    # 積表示・剛性
    for n0 in [7, 27, 703, 2 ** 40 + 1, 87 ** 7]:
        check_product_formula(n0 | 1, 60)
        check_rigidity(n0 | 1, 60)
    # -1 mod 2^m 障壁補題: m <= 14 × t <= 200 全数 + 大きい乱択
    for m in range(2, 15):
        for t in range(1, 201):
            check_minus_one_lemma(m, t)
    for _ in range(200):
        check_minus_one_lemma(random.randint(2, 200), random.randint(1, 10 ** 30))
    # Terras 全単射 k <= 12
    for k in range(1, 13):
        check_terras_bijection(k)
    # 小範囲全数降下
    verify_range(10 ** 6)
    print("collatz.py: all self-checks passed "
          "(product formula, rigidity identity, -1 mod 2^m barrier lemma, "
          "Terras bijection k<=12, descent verified for odd n <= 1e6)")
