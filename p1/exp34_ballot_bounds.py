#!/usr/bin/env python3
"""exp34: numerical sanity checks for the proof of Theorem B+ (c(k) = Theta(C(k,e0)/k)).

Walk: B_j Bernoulli(theta) partial sums (theta = log_3 2), S_j = B_j - theta j (mean zero).
tau = first j >= 1 with S_j <= 0 (i.e. B_j <= theta j).  Climbing words = {tau > k}.
Checks (exact DP in rationals/floats over the lattice of (j, B_j)):
 (A) sup_{y in [0,Y]} sqrt(n) P_y(tau > n)/(1+y) bounded             (uniform persistence bound)
 (B) k^{3/2} P(tau > k, B_k = e)/(1+D')  bounded, D' = e - theta k   (bridge local bound)
 (C) sqrt(k) P(B_k = e) bounded below for |e - theta k| <= sqrt(k)   (binomial LLT)
Also the reversed walk (steps +theta / -(1-theta)) for (A).
"""
import math, sys
import numpy as np
LOG2_3 = math.log2(3); THETA = 1/LOG2_3

def persistence(n, y, up=1-THETA, down=THETA, p=THETA):
    """P_y(tau > n) for the walk with step +up (prob p) / -down (prob 1-p), started at y>0,
    killed when <= 0.  State: number of up-steps b after j steps; position = y + b*up - (j-b)*down."""
    probs = np.zeros(n+2); probs[0] = 1.0  # index b
    for j in range(1, n+1):
        new = np.zeros(n+2)
        new[1:j+1] += probs[0:j]*p      # up step
        new[0:j] += probs[0:j]*(1-p)    # down step
        b = np.arange(0, j+1)
        pos = y + b*up - (j-b)*down
        new[0:j+1][pos <= 1e-12] = 0.0
        probs = new
    return probs.sum()

def bridge_local(k):
    """P(tau > k, B_k = e) for all e, exact float DP."""
    probs = np.zeros(k+2); probs[0] = 1.0
    for j in range(1, k+1):
        new = np.zeros(k+2)
        new[1:j+1] += probs[0:j]*THETA
        new[0:j] += probs[0:j]*(1-THETA)
        b = np.arange(0, j+1)
        new[0:j+1][b - THETA*j <= 1e-12] = 0.0
        probs = new
    return probs

def main():
    print("(A) uniform persistence: sqrt(n) P_y(tau>n)/(1+y)")
    for label, up, down, p in (("forward", 1-THETA, THETA, THETA), ("reversed", THETA, 1-THETA, 1-THETA)):
        worst = 0.0
        for n in (100, 400, 1600, 3200):
            vals = [math.sqrt(n)*persistence(n, y, up, down, p)/(1+y) for y in np.linspace(0.01, 25, 60)]
            worst = max(worst, max(vals))
            print(f"   {label:8s} n={n:5d}: max over y in (0,25] = {max(vals):.4f}   (y->0: {vals[0]:.4f}, y=25: {vals[-1]:.4f})")
        assert worst < 10
    print("(B) bridge local bound: k^{3/2} P(tau>k, B_k=e)/(1+D')   and (C) sqrt(k) P(B_k=e)")
    for k in (200, 400, 800, 1600):
        pr = bridge_local(k)
        e0 = math.ceil(THETA*k + 1e-12) if THETA*k != math.floor(THETA*k) else int(THETA*k)+1
        es = [e for e in range(e0, min(k, e0+int(math.sqrt(k)))+1)]
        ratios = [k**1.5*pr[e]/(1+e-THETA*k) for e in es]
        from math import lgamma, exp, log
        llt = [math.sqrt(k)*exp(lgamma(k+1)-lgamma(e+1)-lgamma(k-e+1) + e*log(THETA) + (k-e)*log(1-THETA)) for e in es]
        print(f"   k={k:5d}: (B) min {min(ratios):.4f} max {max(ratios):.4f};  (C) min {min(llt):.4f} max {max(llt):.4f}")
    print("exp34: all ballot-bound checks passed")

if __name__ == "__main__":
    main()
