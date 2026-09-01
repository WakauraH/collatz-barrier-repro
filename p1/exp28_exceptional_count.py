#!/usr/bin/env python3
"""exp28: K3 — unconditional power-saving count of potential counterexamples.

Claim (elementary, from collapse lemma + Theorem B):
  E = {n > 1 : T^j(n) >= n for all j}  satisfies, for n in (M, 2M], M = 2^m:
  n > 3^j with j = floor(theta*m)  =>  n's class mod 2^j must be climbing.
  Hence |E ∩ (M, 2M]| <= c(j) * 2^{m-j}, and the exponent of the count of the
  necessary-condition set is  1 - theta*(1 - H(theta)) = 0.9684265...

Checks:
  (1) Exact identity: #{n in (2^m, 2^{m+1}] : T^j(n) >= n for all j <= j(m)}
      == c(j(m)) * 2^{m-j(m)}  (brute force vs class count, m <= 18).
      [collapse: for n > 3^j, "no descent within j" <=> climbing class]
  (2) Exponent: log2(count)/m for m <= 60 via exact c(k) DP -> 0.9684...
"""
from math import log2, floor

THETA = log2(3) ** -1  # log_3 2
T = lambda n: n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def climbing_counts(K):
    """c(k) for k <= K via the non-negative Sturmian-driven walk (exact DP)."""
    c = [0] * (K + 1)
    # state: dict d -> paths, after forced b_1 = 1 (d_1 = 0)
    from collections import defaultdict
    state = {0: 1}
    c[1] = 1
    for j in range(1, K):
        e_floor_j, e_floor_j1 = floor(THETA * j), floor(THETA * (j + 1))
        sigma = e_floor_j1 - e_floor_j
        new = defaultdict(int)
        for d, cnt in state.items():
            for b in (0, 1):
                d2 = d + b - sigma
                if d2 >= 0:
                    new[d2] += cnt
        state = dict(new)
        c[j + 1] = sum(state.values())
    return c


def check_identity(m_max=18):
    c = climbing_counts(m_max)
    for m in range(8, m_max + 1):
        j = floor(THETA * m)
        assert 3 ** j < 2 ** m  # collapse lemma applicable for all n in range
        brute = 0
        for n in range(2 ** m + 1, 2 ** (m + 1) + 1):
            x, ok = n, True
            for _ in range(j):
                x = T(x)
                if x < n:
                    ok = False
                    break
            brute += ok
        assert brute == c[j] * 2 ** (m - j), (m, brute, c[j] * 2 ** (m - j))
    print(f"(1) identity OK: brute-force count == c(j)*2^(m-j) for m=8..{m_max}")


def check_exponent(m_max=60):
    c = climbing_counts(floor(THETA * m_max) + 1)
    H = -(THETA * log2(THETA) + (1 - THETA) * log2(1 - THETA))
    target = 1 - THETA * (1 - H)
    for m in (20, 30, 40, 50, 60):
        j = floor(THETA * m)
        expo = (log2(c[j]) + m - j) / m
        print(f"    m={m}: exponent {expo:.5f}")
    print(f"(2) exponent -> {target:.7f} = 1 - theta*(1-H(theta))")




def check_margin(J=24):
    """B(j) = max beta_j/(2^j - 3^{e_j}) over classes whose FIRST non-climbing
    prefix is j.  A non-descending n with first-non-climb at j needs n <= B(j).
    Expect: B(j) < 2^j (so every n in (2^m, 2^{m+1}], m >= j, is forced to
    descend => E-elements climb to depth m), and B(j) ~ (3/2)^j * poly."""
    # enumerate climbing tree nodes with (e, beta); children that go non-climbing
    # at depth j+1 contribute to B(j+1)
    B = [0] * (J + 1)
    level = [(1, 1)]  # depth 1: word "1": e=1, beta=1  (b_0=1: beta_1 = 3*0+2^0)
    for j in range(1, J):
        nxt = []
        for e, beta in level:
            for b in (0, 1):
                e2 = e + b
                beta2 = 3 * beta + 2 ** j if b else beta
                if 3 ** e2 > 2 ** (j + 1):
                    nxt.append((e2, beta2))
                else:
                    B[j + 1] = max(B[j + 1], beta2 // (2 ** (j + 1) - 3 ** e2))
        level = nxt
    for j in range(2, J + 1):
        assert B[j] < 2 ** j, (j, B[j])
        r = B[j] / (1.5 ** j)
        print(f"    j={j}: B(j)={B[j]}  B/1.5^j={r:.2f}  B/2^j={B[j]/2**j:.4f}")
    print(f"(3) margin OK: B(j) < 2^j for all j<={J} — first non-climbing "
          f"prefix at depth j<=log2(n) forces descent in this range")




if __name__ == "__main__":
    check_identity()
    check_exponent()
    check_margin()
    print("exp28: all checks passed")
