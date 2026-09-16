#!/usr/bin/env python3
"""exp32: regression checks for the passages rewritten after the pre-submission review.

(1) P1 Corollary (counting): for n in (M,2M], M=2^m, whose first m iterates all stay >= n,
    the number e of odd steps satisfies e >= m*theta_M, theta_M = log2/log(3+1/M); and
    #{such n} <= sum_{e>=m theta_M} C(m,e) <= 2^{m H(theta_M)}.   (this set contains E cap (M,2M])
(2) P2 Lemma 9.2 (pair spacing): odd seeds w1,w2 of chains of depth >= h in row d
    (|w| <= eps 3^d / 2^h) at positions e1<e2 satisfy e2-e1 >= log2(2^h/eps - 1); checked
    exhaustively over full periods, linearly and cyclically, and the OLD bound 2*alpha*h - c
    is shown to fail.
(3) P2 l^4 identity: sum_{3 !| xi} |ghat(xi)|^4 = 3^m P(Z=0 mod 3^m) - 3^{m-1} P(Z=0 mod 3^{m-1}),
    Z = X1+X2-X3-X4, exact (truncated-geometric) Syracuse law, m<=4.
(4) P2 Theorem 4.1: weight 2^{-lambda u} gives row sum 3^lambda/(2^{1+lambda}-1), min = 2^{-I0}.
(5) P2 Theorem 5.1: E[A log A] = (1/3) log(27/16), tail constant C = 1/log(27/16); Monte Carlo t*P(Y>t).
"""
import math, itertools, numpy as np
from math import comb, log, log2

LOG2_3 = log2(3); THETA = 1/LOG2_3
H = lambda p: -p*log2(p)-(1-p)*log2(1-p)
I0 = (1-H(THETA))/THETA

def check_counting(mmax=22):
    print("(1) counting corollary")
    for m in range(8, mmax+1):
        M = 1 << m
        n = np.arange(M+1, 2*M+1, dtype=np.int64)
        x = n.copy(); alive = np.ones(M, bool); e = np.zeros(M, np.int64)
        for _ in range(m):
            odd = (x & 1) == 1
            e += odd & alive
            x = np.where(odd, (3*x+1)//2, x//2)
            alive &= x >= n
        thetaM = log(2)/log(3+1/M)
        emin = math.ceil(m*thetaM - 1e-12)
        cnt = int(alive.sum())
        assert e[alive].min() >= m*thetaM - 1e-9, (m, e[alive].min(), m*thetaM)
        S = sum(comb(m, k) for k in range(emin, m+1))
        assert cnt <= S <= 2**(m*H(thetaM)) + 1e-9, (m, cnt, S)
        print(f"  m={m:2d}: #stay>=n for m steps = {cnt:7d}  <= sum C(m,e>={emin}) = {S:8d}  <= 2^(mH(theta_M)) = {2**(m*H(thetaM)):10.1f};  cnt/M^H = {cnt/M**H(THETA):.3f}")

def signed(v, N):
    v %= N
    return v - N if v > N//2 else v

def check_pair(dmax=9):
    print("(2) pair-spacing lemma")
    ALPHA = LOG2_3
    old_fail = 0; new_fail = 0; pairs = 0
    for d in range(2, dmax+1):
        N = 3**d; per = 2*3**(d-1)
        v = [signed(pow(2, e, N), N) for e in range(per)]
        for eps in (0.5, 0.25, 0.1):
            for h in range(1, int(log2(eps*N))+1):
                pos = [e for e in range(per) if v[e] % 2 == 1 and abs(v[e]) <= eps*N/2**h]
                bound_new = log2(2**h/eps - 1)
                bound_old = 2*ALPHA*h - log2((1+eps)/eps)
                for i, j in itertools.combinations(range(len(pos)), 2):
                    for D in (pos[j]-pos[i], per-(pos[j]-pos[i])):
                        pairs += 1
                        if D < bound_new - 1e-9: new_fail += 1
                        if D < bound_old - 1e-9: old_fail += 1
    print(f"  pairs checked: {pairs}; violations of new bound: {new_fail}; violations of OLD bound 2*alpha*h-c: {old_fail}")
    assert new_fail == 0

def syracuse_law(m, A=40):
    N = 3**m
    # X = sum_{j=1}^m 3^{m-j} 2^{-(a_1+...+a_j)} mod 3^m, a_i iid Geom(1/2) on {1,2,...}
    inv2 = pow(2, -1, N)
    dist = {0: 1.0}  # distribution of partial sums; build recursively in j
    # state: (X_partial, S = a_1+..+a_j mod ord) -> prob ; ord of 2 mod 3^m is 2*3^(m-1)
    ordr = 2*3**(m-1)
    state = {(0, 0): 1.0}
    for j in range(1, m+1):
        new = {}
        for (X, S), p in state.items():
            for a in range(1, A+1):
                pa = 2.0**-a
                S2 = (S + a) % ordr
                X2 = (X + 3**(m-j) * pow(inv2, S2, N)) % N
                new[(X2, S2)] = new.get((X2, S2), 0.0) + p*pa
        state = new
    law = np.zeros(N)
    for (X, S), p in state.items(): law[X] += p
    return law / law.sum()

def check_l4(mmax=4):
    print("(3) l^4 identity")
    for m in range(1, mmax+1):
        N = 3**m; law = syracuse_law(m)
        ghat = np.fft.fft(law)  # ghat[xi] = sum_x law[x] e(-xi x/N)
        lhs = sum(abs(ghat[xi])**4 for xi in range(N) if xi % 3 != 0)
        conv = np.real(np.fft.ifft(np.fft.fft(law)**2 * np.conj(np.fft.fft(law))**2))  # law of X1+X2-X3-X4
        pz = conv[0]
        # mod 3^{m-1}: Z = 0 mod 3^{m-1}
        pz1 = sum(conv[z] for z in range(N) if z % 3**(m-1) == 0) if m > 1 else 1.0
        rhs = N*pz - (N//3)*pz1
        print(f"  m={m}: LHS={lhs:.10f}  RHS={rhs:.10f}  diff={lhs-rhs:.2e}")
        assert abs(lhs-rhs) < 1e-9

def check_weight():
    print("(4) weighted row sum / sign")
    f = lambda lam: sum(2.0**-a * 2.0**(lam*(LOG2_3 - a)) for a in range(1, 200))
    g = lambda lam: 3**lam/(2**(1+lam)-1)
    for lam in (-0.5, 0.0, 0.438, 1.0):
        assert abs(f(lam)-g(lam)) < 1e-12
    lams = np.linspace(-0.9, 3, 400001); vals = g(lams); i = vals.argmin()
    print(f"  f(lambda)=3^l/(2^(1+l)-1) verified; min f = {vals[i]:.10f} = 2^-{-log2(vals[i]):.7f} at lambda*={lams[i]:.5f}  (2^-I0 = {2**-I0:.10f}, I0={I0:.7f})")
    assert abs(-log2(vals[i]) - I0) < 1e-5

def check_kesten(nsamp=2_000_000, seed=1):
    print("(5) Kesten tail constant")
    EAlogA = sum(2.0**-a * 3*2.0**-a * log(3*2.0**-a) for a in range(1, 200))
    print(f"  E[A log A] = {EAlogA:.10f}  vs (1/3)log(27/16) = {log(27/16)/3:.10f};  C = 1/log(27/16) = {1/log(27/16):.10f}")
    assert abs(EAlogA - log(27/16)/3) < 1e-12
    rng = np.random.default_rng(seed)
    # Y = sum_n B_n prod_{i<n} A_i with A = 3*2^-a, B = 2^-a  (a Geom(1/2)); simulate 400 terms
    Y = np.zeros(nsamp); P = np.ones(nsamp)
    for _ in range(400):
        a = rng.geometric(0.5, nsamp)
        Y += P * 2.0**-a
        P *= 3*2.0**-a
    for t in (20, 50, 100, 200):
        print(f"  t={t:4d}: t*P(Y>t) = {t*np.mean(Y>t):.3f}")

if __name__ == "__main__":
    check_counting(); check_pair(); check_l4(); check_weight(); check_kesten()
    print("exp32: all regression checks passed")
