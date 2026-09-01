#!/usr/bin/env python3
"""exp29: verification of the valuation-size identity and the geometric law
on full periods (Theorem "geometric law on cycles" in P2).

  (1) Identity: nu_2(r(K)) >= sigma  <=>  |r(K - sigma)| <= M/2^{sigma+1},
      exhaustively over the full period of 2 mod 3^m, sigma <= 6, m <= 12.
  (2) Geometric law: P(nu_2 >= sigma) over the full period = 2^{-sigma} + O(2^sigma/3^m),
      and the ball-conditioned version at epsilon = 0.1.
"""


def signed(x, M):
    x %= M
    return x - M if x > M - x else x  # representative in (-M/2, M/2]


def nu2(x):
    x = abs(x)
    s = 0
    while x % 2 == 0:
        x //= 2
        s += 1
    return s


def check(m):
    M = 3 ** m
    period = 2 * 3 ** (m - 1)
    r = [signed(pow(2, K, M), M) for K in range(period)]
    # (1) identity
    for K in range(period):
        for s in range(7):
            lhs = nu2(r[K]) >= s
            rhs = abs(r[(K - s) % period]) <= M / 2 ** (s + 1)
            assert lhs == rhs, (m, K, s)
    # (2) geometric law, full period and ball-conditioned
    for eps in (0.5, 0.1):
        inball = [x for x in r if abs(x) <= eps * M]
        if len(inball) < 64:
            continue  # counting error term dominates in tiny balls
        freqs = [sum(1 for x in inball if nu2(x) >= s) / len(inball)
                 for s in range(1, 5)]
        for s, fr in enumerate(freqs, 1):
            assert abs(fr - 2 ** -s) < 2 ** s / (eps * M) + 1e-12, (m, eps, s, fr)
        if m == 12:
            print(f"  m={m} eps={eps}: P(nu2>=s) = " +
                  "/".join(f"{fr:.4f}" for fr in freqs) + "  (geometric: 0.5/0.25/0.125/0.0625)")


if __name__ == "__main__":
    for m in range(2, 13):
        check(m)
    print("exp29: valuation-size identity exhaustive (m<=12, sigma<=6): zero mismatches;")
    print("       geometric law within counting error, full period and ball-conditioned")
