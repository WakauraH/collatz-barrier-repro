#!/usr/bin/env python3
"""exp27: K4 — adaptive/disjunctive certificate systems collapse to the canonical tree.

Pre-registered expectations (all algebraically proven; this is the independent check):
  (1) Adaptive collapse: for every n, T^j(n) > n at every climbing prefix j (no size
      condition); at the first non-climbing prefix j1, descent holds whenever n > 3^j1.
      Hence for n > 3^K: descent-within-K  <=>  j1(n mod 2^K) <= K, first passage = j1.
  (2) Persistence: appending parity 1 preserves climbing => c(k+1) >= c(k), and every
      climbing class mod 2^k contains climbing classes at every deeper horizon.
      Cross-check c(20) == 27328 (verify.py anchor).
  (3) Invalidity witness: for any climbing class mod 2^d, any horizon K, and any odd
      modulus q, there are infinitely many n in the class (CRT) with no descent within K.
"""

T = lambda n: n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def parity_vector(r, K):
    """Parities b_0..b_{K-1} of the class r mod 2^K (depend only on r)."""
    n = r if r >= 1 else 2 ** K
    bs = []
    for _ in range(K):
        bs.append(n & 1)
        n = T(n)
    return bs


def j1_of(bs):
    """First j with 3^{e_j} < 2^j, or None if climbing through len(bs)."""
    e = 0
    for j, b in enumerate(bs, 1):
        e += b
        if 3 ** e < 2 ** j:
            return j
    return None


def check_collapse(K=12, N=2 ** 20):
    j1_table = [j1_of(parity_vector(r, K)) for r in range(2 ** K)]
    mism = 0
    for n in range(2, N + 1):
        j1 = j1_table[n % (2 ** K)]
        m, sigma = n, None
        for j in range(1, K + 1):
            m = T(m)
            if m < n:
                sigma = j
                break
        if j1 is None:
            assert sigma is None, (n, sigma)          # climbing: no descent, ANY n
        else:
            assert sigma is None or sigma >= j1, (n, sigma, j1)   # never earlier
            if n > 3 ** j1:
                assert sigma == j1, (n, sigma, j1)    # exact first passage
            elif sigma != j1:
                mism += 1                             # small-n straggler (allowed)
    print(f"(1) collapse OK: K={K}, n<=2^20; stragglers below 3^j1 bound: {mism}")


def climbing_words(K):
    """DFS of the climbing tree; returns count per depth 1..K."""
    counts = [0] * (K + 1)
    stack = [(1, 1)]  # (depth, e) after forced b_1 = 1
    counts[1] = 1
    while stack:
        j, e = stack.pop()
        if j == K:
            continue
        for b in (0, 1):
            e2 = e + b
            if 3 ** e2 > 2 ** (j + 1):
                counts[j + 1] += 1
                stack.append((j + 1, e2))
    return counts


def check_persistence(K=20):
    c = climbing_words(K)
    for k in range(1, K):
        assert c[k + 1] >= c[k], (k, c[k], c[k + 1])  # append-1 injection
    assert c[20] == 27328, c[20]                       # anchor vs verify.py
    print(f"(2) persistence OK: c(k) nondecreasing, c(20)={c[20]} matches verifier")


def check_invalidity_witness():
    for d, K, q, a in [(6, 40, 5, 2), (10, 60, 7, 3), (14, 80, 11, 1)]:
        # class -1 mod 2^d is climbing; witnesses: n ≡ -1 mod 2^{K+2}, n ≡ a mod q
        step, n = q * 2 ** (K + 2), None
        base = 2 ** (K + 2) - 1
        while n is None:
            base += 2 ** (K + 2)
            if base % q == a:
                n = base
        for t in range(3):
            m0 = n + t * step
            m = m0
            for _ in range(K):
                m = T(m)
                assert m > m0, (d, K, q, m0)
    print("(3) invalidity witnesses OK: climbing ∩ odd-modulus classes never "
          "descend within horizon (sampled d,K,q)")


if __name__ == "__main__":
    check_collapse()
    check_persistence()
    check_invalidity_witness()
    print("exp27: all adaptive-barrier checks passed")
