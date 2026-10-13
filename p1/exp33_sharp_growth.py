#!/usr/bin/env python3
"""exp33: sharp growth of c(k) -- is c(k) = Theta(C(k,e0)/k) = Theta(2^{H k} k^{-3/2})?

Theorem B gives C(k,e0)/k <= c(k) <= (k+1) C(k,e0), a gap of k^2.  Fluctuation theory
(ballot problem for a mean-zero non-lattice walk conditioned on its endpoint) predicts
   N_e := #{climbing words with e ones} = C(k,e) * Theta((1 + D_e)/k),  D_e = e log2(3) - k,
hence c(k) = sum_e N_e = Theta(C(k,e0)/k), i.e. log2 c(k) = H k - (3/2) log2 k + O(1).
We compute exactly (big integers) for k <= KMAX:
  R(k)   = k c(k) / C(k,e0)                      (should be bounded away from 0 and inf)
  Q(k,e) = k N_e / (C(k,e) (1 + D_e))            (should be bounded)
and fit log2 c(k) = H k - c2 log2 k + c0 on k in [K0, KMAX].
"""
import math, sys
from math import comb, log2
from fractions import Fraction
import numpy as np

LOG2_3 = log2(3); THETA = 1/LOG2_3
H = -THETA*log2(THETA) - (1-THETA)*log2(1-THETA)

def climbing_by_ones(K):
    """returns list over k of dict e -> N_e (number of climbing words of length k with e ones)"""
    cur = {0: 1}; out = [dict(cur)]
    for j in range(1, K+1):
        nxt = {}
        for e, cnt in cur.items():
            for e2 in (e, e+1):
                if 3**e2 > (1 << j):
                    nxt[e2] = nxt.get(e2, 0) + cnt
        cur = nxt; out.append(dict(cur))
    return out

def main(KMAX=1200, K0=200):
    N = climbing_by_ones(KMAX)
    ks = range(2, KMAX+1); R = []; Qmax = []; Qmin = []
    for k in ks:
        e0 = next(e for e in range(k+1) if 3**e > 2**k)
        ck = sum(N[k].values())
        R.append(float(Fraction(k*ck, comb(k, e0))))
        qs = []
        for e, Ne in N[k].items():
            D = e*LOG2_3 - k
            qs.append(float(Fraction(k*Ne, comb(k, e)))/(1+D))
        Qmax.append(max(qs)); Qmin.append(min(qs))
    R = np.array(R); ks = np.array(list(ks))
    print(f"R(k) = k c(k)/C(k,e0):  k<=50: min {R[:49].min():.3f} max {R[:49].max():.3f};  "
          f"k in [200,{KMAX}]: min {R[198:].min():.4f} max {R[198:].max():.4f}")
    print(f"Q(k,e) = k N_e/(C(k,e)(1+D_e)) over k in [200,{KMAX}]: min {min(Qmin[198:]):.4f} max {max(Qmax[198:]):.4f}")
    # regression log2 c(k) = H k - c2 log2 k + c0 on [K0, KMAX]
    y = np.array([log2(sum(N[k].values())) - H*k for k in range(K0, KMAX+1)])
    X = np.array([[1.0, -log2(k)] for k in range(K0, KMAX+1)])
    c0, c2 = np.linalg.lstsq(X, y, rcond=None)[0]
    resid = y - (c0 - c2*np.log2(np.arange(K0, KMAX+1)))
    print(f"fit log2 c(k) = H k - c2 log2 k + c0 on [{K0},{KMAX}]: c2 = {c2:.4f}, c0 = {c0:.4f}, resid range [{resid.min():.3f},{resid.max():.3f}]")
    # boundedness test: slope of log2 R(k) against log2 k should be ~0 (R = k c(k)/C(k,e0))
    kk = np.arange(2, KMAX+1); m = kk >= K0
    sl = np.polyfit(np.log2(kk[m]), np.log2(R[m]), 1)[0]
    print(f"slope of log2 R(k) vs log2 k on [{K0},{KMAX}]: {sl:+.4f}  (0 = Theta(C(k,e0)/k); +1 would be Theta(C(k,e0)))")
    # same fit for log2 C(k,e0): expect c2 = 1/2
    y2 = np.array([log2(comb(k, next(e for e in range(k+1) if 3**e > 2**k))) - H*k for k in range(K0, KMAX+1)])
    c0b, c2b = np.linalg.lstsq(X, y2, rcond=None)[0]
    print(f"fit log2 C(k,e0) = H k - c2' log2 k + c0' : c2' = {c2b:.4f} (Stirling: 1/2 plus oscillation from {{k theta}})")
    # oscillation of R with the fractional offset d0 = e0 log2 3 - k in [0, log2 3)
    d0 = np.array([ (next(e for e in range(int(k)+1) if 3**e > 2**int(k)))*LOG2_3 - int(k) for k in ks])
    sel = ks >= 200
    bins = np.linspace(0, LOG2_3, 9)
    print("R vs d0 = e0 log2 3 - k  (k >= 200):")
    for a, b in zip(bins[:-1], bins[1:]):
        m = sel & (d0 >= a) & (d0 < b)
        if m.any(): print(f"  d0 in [{a:.2f},{b:.2f}): mean R {R[m].mean():.4f}  n={m.sum()}")
    # the lower-bound factor E[G]: R(k) = sum_e [C(k,e)/C(k,e0)] * [k N_e / C(k,e)]
    print(f"R(1200 region) sample: k=1000..1005 -> {np.round(R[998:1004],4)}")

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 1200)
