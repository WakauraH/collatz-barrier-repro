"""cyclebound.py — 非自明周期の奇数ステップ数 k に対する下界 (Eliahou 型) の再構成。

U 写像の周期 (奇数元 m_1..m_k, A = sum a_j) の厳密な周期方程式:
    2^A = prod_{j=1}^{k} (3 + 1/m_j)                     … (C)
ゆえに 3^k < 2^A <= (3 + 1/M)^k,  M = min_j m_j.
計算検証 (Barina 2020: n < 2^68 は全て 1 へ到達) より M > 2^68。
よって  0 < A - k*log2(3) <= k * log2(1 + 1/(3M)) =: k*delta.
A = ceil(k log2 3) なので、k が排除されない必要条件は ||k*theta||^+ <= k*delta
(theta = log2 3 の整数上方距離)。連分数の最良近似性:
   q_j <= k < q_{j+1}  ⇒  ||k theta|| >= ||q_j theta||
を使い、すべての k < K* を排除する最大の K* を求める。

厳密性の担保:
 - theta は Decimal 160 桁で計算し、±1e-140 のガード帯付きで扱う。
 - 連分数の各収束分数 p/q は、q <= 2*10^5 の範囲で 2^p vs 3^q の
   厳密整数比較により検証する (それ以降は 160 桁精度に依存、誤差余裕 >> 1e-100)。
 - delta も上側に丸めて使用。
"""
from decimal import Decimal, getcontext

getcontext().prec = 160


def exact_side(p: int, q: int) -> int:
    """sign(p - q*log2 3) を厳密整数比較で返す: 2^p vs 3^q."""
    a, b = 1 << p, 3 ** q
    return (a > b) - (a < b)


def main(log2M: int):
    theta = Decimal(3).ln() / Decimal(2).ln()
    guard = Decimal(10) ** -140

    # 連分数展開 (Decimal ベース) + 小さい q の厳密照合
    cf, conv = [], []
    x = theta
    p2, p1 = 0, 1  # p_{-2}? 標準初期化: p_{-1}=1,p_{-2}=0 / q_{-1}=0,q_{-2}=1
    q2, q1 = 1, 0
    for _ in range(40):
        a = int(x)
        cf.append(a)
        p = a * p1 + p2
        q = a * q1 + q2
        conv.append((p, q))
        p2, p1, q2, q1 = p1, p, q1, q
        frac = x - a
        if frac < guard * 10 ** 20:
            break
        x = 1 / frac
        if q > 10 ** 16:
            break
    # 厳密照合: 収束分数は交互に上下から近似する (q が小さい範囲)
    for i, (p, q) in enumerate(conv):
        if q > 2 * 10 ** 5 or q == 0:
            continue
        s = exact_side(p, q)
        # 偶数番目 (i=0,2,..) は下から (p/q < theta ⇒ 2^p < 3^q)
        expect = -1 if i % 2 == 0 else 1
        assert s == expect, (i, p, q, s)
    print("連分数 (先頭):", cf[:20])

    M = Decimal(2) ** log2M
    delta = (1 + 1 / (3 * M)).ln() / Decimal(2).ln() + guard  # 上側丸め

    # 排除: 区間 [q_j, q_{j+1}) の k は ||k theta|| >= ||q_j theta|| - guard.
    # 条件 k*delta < ||q_j theta|| が区間の最大 k = q_{j+1}-1 で成立すれば区間全体排除。
    kmin = None
    for j in range(len(conv) - 1):
        pj, qj = conv[j]
        qn = conv[j + 1][1]
        if qj == 0:
            continue
        dist = abs(qj * theta - pj) - guard
        if (Decimal(qn - 1) * delta) < dist:
            continue  # 区間 [qj, qn) 全体を排除
        # この区間から排除が破れうる。最小の破れ k を線形には探せないので
        # 保守的に k >= dist/delta を報告 (それ未満は排除)。
        kmin = int(dist / delta)
        # 有効範囲は k < qn に限る
        kmin = min(kmin, qn - 1)
        print(f"排除が破れうる最初の区間: [q_{j}={qj}, q_{j+1}={qn})")
        break
    assert kmin is not None
    L = (1 + theta)  # 周期の全 T ステップ ≈ k(1+log2 3) 以上 (A >= k theta)
    print(f"M > 2^{log2M} のとき: 非自明周期の奇数ステップ数 k >= {kmin:,}")
    print(f"  ⇒ 周期の全 T-ステップ長 >= k*(1+log2 3) ≈ {int(kmin * float(L)):,}")


if __name__ == "__main__":
    for log2M in (68, 71):
        print(f"--- 最小元下界 M > 2^{log2M} ---")
        main(log2M)
        print()
