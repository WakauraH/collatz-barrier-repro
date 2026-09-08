#!/usr/bin/env python3
"""exp30: rigorous (error-accounted) per-frequency upper bounds |g_m(2^k)| <= U_m(k)
from Tao's product inequality (7.5), on the full extended window, for m = 64/128/256.

What is certified (unconditionally, for the scanned k only):
    |g_m(2^k)| <= B_m(k) := E prod_{j<=m/2} |f(3^{2j-2} 2^{k-l_j}, b_j)|   (Tao 2022, (7.5))
and B_m(k) <= U_m(k), with every approximation pushed to the upper side:
  * b-truncation (b > B):  + (m/2) * sum_{b>B} (b-1) 2^{-b}   [union bound, |f| <= 1];
    B = B(m) is chosen so that this tail is below 2^{-(0.35 m + 8)}, i.e. far below the
    deepest band bound, so it never limits a certified rate.
  * pruned DP states:      + exact dropped mass (true scale)   [future factors <= 1];
    the relative threshold is 2^{-(0.4m+40)} (m-adaptive) so the added-back mass stays
    far below the deepest band bound and never limits a certified rate.
  * floating point:        each |f| gets +EPS_W; final total * (1+EPS_DP)
    (libm cos/sin on reduced arguments are accurate to ~1e-16; EPS_W = 1e-11 covers
     B terms with 1e-13 slack each; EPS_DP = 1e-8 covers the ~1e5-deep chains of
     nonnegative float sums/products at 2^-53 relative error each, by a factor >100.)
Implementation: for each target valuation l2 the phases y_t = 3^{2j-2} 2^{k-l2} (2^t+3)
are computed once and prefix-summed, giving |f(x, b)| for all b simultaneously.

What is NOT certified: frequencies outside the scanned window. Any statement about
delta_m itself rests on window localization of the extremal frequency (exhaustively
verified for m <= 15 only).
"""
import math
import sys
from fractions import Fraction

import numpy as np

LOG2_3 = math.log2(3)
EPS_W = 1e-11
EPS_DP = 1e-8


def prune_for(m):
    """Relative pruning threshold: the dropped mass (added back exactly) must stay far
    below the deepest band bound ~2^{-0.35 m}; 2^{-(0.4m+40)} leaves >2^{-40} headroom."""
    return min(1e-22, 2.0 ** (-(0.4 * m + 40)))


def tail_prob(m, B):
    """Upper bound on (m/2) * P(b > B), exact rational -> float (rounded up)."""
    t = sum(Fraction(b - 1, 2 ** b) for b in range(B + 1, B + 200))
    t += Fraction(1, 2 ** (B + 180))          # remainder beyond B+199
    return float(Fraction(m, 2) * t) * (1 + 1e-12)


def bmax_for(m):
    B = 40
    while tail_prob(m, B) >= 2.0 ** (-(0.35 * m + 8)):
        B += 1
    return B


def rigorous_bound(m, k, B):
    """Return U_m(k): certified upper bound on |g_m(2^k)|."""
    M3 = 3 ** m
    inv2 = pow(2, -1, M3)
    steps = m // 2
    Pb = np.array([(b - 1) / 2.0 ** b for b in range(2, B + 1)])   # exact dyadics
    bs = np.arange(2, B + 1)
    lmax = steps * B
    pows = {}
    v = pow(2, k, M3) if k >= 0 else pow(inv2, -k, M3)
    pows[k] = v
    for e in range(k - 1, k - lmax - B - 1, -1):
        v = (v * inv2) % M3
        pows[e] = v
    smalls = [(2 ** t + 3) for t in range(1, B)]
    two_pi = 2.0 * math.pi
    PRUNE = prune_for(m)
    V = {0: 1.0}
    logscale = 0.0
    dropped = 0.0
    for j in range(1, steps + 1):
        p3 = pow(3, 2 * (j - 1), M3)
        lo, hi = min(V), max(V)
        l2s = range(lo + 2, hi + B + 1)
        nxt = {}
        for l2 in l2s:
            # predecessors l = l2 - b for b in 2..B
            vals = np.array([V.get(l2 - b, 0.0) for b in range(2, B + 1)])
            if not vals.any():
                continue
            base = (pows[k - l2] * p3) % M3
            frac = np.array([((base * s) % M3) / M3 for s in smalls])   # t = 1..B-1
            ph = np.exp(-1j * two_pi * frac)
            S = np.cumsum(ph)                                            # S_b, b = 2..B
            w = np.minimum(1.0, np.abs(S) / (bs - 1) + EPS_W)
            nxt[l2] = float(np.sum(vals * Pb * w))
        mx = max(nxt.values())
        keep = {}
        for l, x in nxt.items():
            if x > PRUNE * mx:
                keep[l] = x
            else:
                dropped += x * 2.0 ** logscale
        V = keep
        logscale += math.log2(mx)
        for l in V:
            V[l] /= mx
    total = sum(V.values()) * 2.0 ** logscale
    return total * (1 + EPS_DP) + dropped * (1 + EPS_DP) + tail_prob(m, B)


def r_of_mu(mu):
    return mu * LOG2_3 + math.log2(2 ** (1 - mu) - 1)


if __name__ == "__main__":
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 64
    B = bmax_for(m)
    KLO, KHI = -80, int(1.66 * m) + 20
    print(f"exp30: m={m}, B(m)={B} (tail {tail_prob(m, B):.2e} = 2^{math.log2(tail_prob(m, B)):.1f}),"
          f" window k in [{KLO},{KHI}] ({KHI-KLO+1} freqs)")
    rates = {}
    for k in range(KLO, KHI + 1):
        U = rigorous_bound(m, k, B)
        rates[k] = -math.log2(U) / m
    a_min = min(rates.values())
    k_min = min(rates, key=rates.get)
    print(f"  certified: sup_(window) |g_{m}(2^k)| <= 2^(-{a_min:.5f}*{m}) = 2^(-{a_min*m:.2f})"
          f"   (attained at k={k_min}, u={k_min - m*LOG2_3:+.1f})")
    zones = {"seam/deep": [], "mid": [], "shoulder": [], "line±": [], "wrap": []}
    for k, a in rates.items():
        u = k - m * LOG2_3
        if k < 0.3 * m * LOG2_3: zones["seam/deep"].append(a)
        elif u < -0.15 * m: zones["mid"].append(a)
        elif u < -8: zones["shoulder"].append(a)
        elif u <= 2: zones["line±"].append(a)
        else: zones["wrap"].append(a)
    for z, arr in zones.items():
        print(f"  {z:10s}: min={min(arr):.4f}  n={len(arr)}")
    best = None
    for mu100 in range(-1, -45, -1):
        mu = mu100 / 100.0
        r = r_of_mu(mu)
        ok = all(r + abs(mu) * abs(k - m * LOG2_3) / m <= a
                 for k, a in rates.items() if not (-8 <= k - m * LOG2_3 <= 2))
        if ok and (best is None or r > best[1]):
            best = (mu, r)
    if best:
        mu, r = best
        slack = min(a - (r + abs(mu) * abs(k - m*LOG2_3)/m)
                    for k, a in rates.items() if not (-8 <= k - m*LOG2_3 <= 2))
        print(f"  constraint system (certified rates, zero margin): mu={mu:.2f}, r={r:.4f},"
              f" min slack {slack:+.4f}")
    print("  NOTE: statements above cover the scanned window only; delta_m itself needs"
          " window localization of the extremal frequency (exhaustive for m<=15).")
