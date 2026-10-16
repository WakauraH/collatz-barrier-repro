#!/usr/bin/env python3
"""exp35: the O(1) fluctuation of c(k) is a function of {theta k} alone.

Theorem B+ gives R(k) := k c(k)/C(k,e0) = Theta(1), e0 = ceil(theta k).  Fluctuation theory
predicts the exact law
    R(k) -> F(delta0),  delta0 := e0 - theta k = 1 - {theta k} in (0,1),
    F(delta0) = sum_{j>=0} rho^j Lambda(delta0 + j),  rho = (1-theta)/theta,
    Lambda(D') := lim_k k P(tau > k | B_k = theta k + D')   (ballot limit),
and Lambda(x) is proportional to the renewal function V^(x) of the descending ladder
heights of the REVERSED walk (steps +theta w.p. 1-theta, -(1-theta) w.p. theta).
Checks:
 (A) collapse: within-bin spread of R(k) vs delta0 shrinks as k grows;
 (B) Lambda(D') from the exact bridge DP (k = 1600) vs V^(D') from the ladder-height DP:
     ratio constant across D' in (0, 6];
 (C) F(delta0) assembled from Lambda vs observed R(k).
"""
import math, sys
from math import comb, log2
from fractions import Fraction
import numpy as np
LOG2_3 = log2(3); THETA = 1/LOG2_3; RHO = (1-THETA)/THETA

def climbing_by_ones(K):
    cur = {0: 1}; out = [dict(cur)]
    for j in range(1, K+1):
        nxt = {}
        for e, cnt in cur.items():
            for e2 in (e, e+1):
                if 3**e2 > (1 << j): nxt[e2] = nxt.get(e2, 0) + cnt
        cur = nxt; out.append(dict(cur))
    return out

def e0_of(k): return next(e for e in range(k+1) if 3**e > 2**k)

def bridge_local(k):
    probs = np.zeros(k+2); probs[0] = 1.0
    for j in range(1, k+1):
        new = np.zeros(k+2)
        new[1:j+1] += probs[0:j]*THETA; new[0:j] += probs[0:j]*(1-THETA)
        b = np.arange(0, j+1); new[0:j+1][b - THETA*j <= 1e-12] = 0.0
        probs = new
    return probs

def binom_pmf(k, e):
    from math import lgamma, exp, log
    return exp(lgamma(k+1)-lgamma(e+1)-lgamma(k-e+1) + e*log(THETA) + (k-e)*log(1-THETA))

def ladder_renewal(xmax=8.0, nsteps=40000, grid=4000):
    """V^(x) = E #{i>=0: H_1+..+H_i <= x} for descending ladder heights of the reversed walk.
    Ladder height distribution via DP: first passage of S^ = j*theta - b below 0 (b = #down steps);
    H = -(S^ at passage) in (0, 1-theta].  Then renewal function by discretized convolution."""
    # first-passage law: state b after j steps with all previous positions > 0 (start 0, tau>=1)
    probs = {0: 1.0}; H = {}
    for j in range(1, nsteps+1):
        new = {}
        for b, p in probs.items():
            # up step
            new[b] = new.get(b, 0.0) + p*(1-THETA)
            # down step
            pos = j*THETA - (b+1)
            if pos < 0: H[-pos] = H.get(-pos, 0.0) + p*THETA
            else: new[b+1] = new.get(b+1, 0.0) + p*THETA
        probs = {b: p for b, p in new.items() if p > 1e-20}
    mass = sum(H.values()); mean = sum(h*p for h, p in H.items())
    # renewal function on a grid
    dx = xmax/grid; V = np.zeros(grid+1); V[:] = 1.0   # i = 0 term
    dist = np.zeros(grid+1); dist[0] = 1.0            # law of H_1+..+H_i (i=0: delta at 0)
    hgrid = np.zeros(grid+1)
    for h, p in H.items(): hgrid[min(grid, int(round(h/dx)))] += p
    for i in range(1, 200):
        dist = np.convolve(dist, hgrid)[:grid+1]
        V += np.cumsum(dist)
        if dist.sum() < 1e-12: break
    return V, dx, mass, mean

def main(KMAX=1200):
    N = climbing_by_ones(KMAX)
    ks = np.arange(2, KMAX+1)
    R = np.array([float(Fraction(int(k)*sum(N[int(k)].values()), comb(int(k), e0_of(int(k))))) for k in ks])
    d0 = np.array([e0_of(int(k)) - THETA*int(k) for k in ks])
    print("(A) collapse of R(k) onto delta0 = e0 - theta k: within-bin std (10 bins)")
    bins = np.linspace(0, 1, 11)
    for lo, hi in ((100, 300), (300, 600), (600, 1200)):
        m = (ks >= lo) & (ks < hi); stds = []; means = []
        for a, b in zip(bins[:-1], bins[1:]):
            mm = m & (d0 >= a) & (d0 < b)
            if mm.sum() > 2: stds.append(R[mm].std()); means.append(R[mm].mean())
        print(f"   k in [{lo},{hi}): mean within-bin std {np.mean(stds):.3f}  (bin means {np.round(means,2)})")
    print("(B) Lambda(D') = k P(tau>k | B_k = e) at k=1600 vs ladder renewal function V^(D')")
    k = 1600; pr = bridge_local(k); e0 = e0_of(k)
    V, dx, mass, mean = ladder_renewal()
    print(f"   ladder height law: total mass {mass:.6f}, mean {mean:.5f}")
    rows = []
    for e in range(e0, e0+7):
        D = e - THETA*k; lam = k*pr[e]/binom_pmf(k, e); v = V[int(round(D/dx))]
        rows.append((D, lam, v, lam/v))
        print(f"   D'={D:.3f}: Lambda={lam:.4f}  V^={v:.4f}  ratio={lam/v:.4f}")
    ratio = np.mean([r[3] for r in rows])
    print("(C) F(delta0) = sum_j rho^j Lambda(delta0+j) vs observed R(k), k in [1000,1200]")
    for k in range(1000, 1201, 40):
        e0 = e0_of(k); dl = e0 - THETA*k
        F = sum(RHO**j * ratio * V[min(len(V)-1, int(round((dl+j)/dx)))] for j in range(0, 8))
        print(f"   k={k}: delta0={dl:.3f}  R(k)={R[k-2]:.3f}  F={F:.3f}  ratio {R[k-2]/F:.3f}")

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 1200)
