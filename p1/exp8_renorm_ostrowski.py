"""exp8_renorm_ostrowski.py — (A) δ_m の第一通過繰り込み等式 (L-δ2 の核) の導出検証
と no-positivity ミニ障害の定量化、(B) Ostrowski 繰り込みの定量化。

(A) 等式 (導出): τ = min{j: A_j > k}, x = 2^k/3^m として
  g_m(k) = E[e(x Y_m); A_m<=k]
         + Σ_{j=0}^{m-1} Σ_{A<=k} amp_j(A) · F(m-j, k-A),
  amp_j(A) = E[e(x Y_j); A_j = A <= k]  (Y_j = Σ_{i<=j} 3^{i-1} 2^{-A_i} は実数),
  F(d, r) = Σ_{a>r} 2^{-a} e_{3^d}(2^{r-a}) · V_{d-1}(2^{r-a})   (V_d(ξ)=E e_{3^d}(ξ X_d)).
  これを m=8, k=12 (および数組) で全周波数稠密計算と 1e-9 精度で照合する。
  さらに no-positivity: E[e(xY_m); A_m<=k] と P(A_m<=k) を比較し、good 事象上でも
  位相が Θ(1) 回転して正定値性が失われることを示す (最終項 2^{k-A_m}/3 >= 1/3 回転)。

(B) Ostrowski: 安定化 float DP で log₂c(k) を k<=30000 まで計算 (k<=400 で厳密値と照合)。
  Δφ(k) = φ(k+1)-φ(k), φ = log₂c - H·k を Sturmian 文字 σ_k に回帰 (R²)、
  残差の積算と不一致度 D(k) = Σ_{j<=k}({jθ}-1/2) の相関を測る。
  収束分母 q_n における φ の値も出力する。
"""
import math
import numpy as np

AMAX = 48
H = 0.9499555271570688  # H(log_3 2)
THETA = math.log(2) / math.log(3)


# ---------- (A) ----------
def dist_X(d: int):
    """X_d mod 3^d の厳密分布 (d ステップで定常)。"""
    if d == 0:
        return np.array([1.0])
    M = 3 ** d
    inv2 = pow(2, -1, M)
    w = 2.0 ** -(np.arange(1, AMAX + 1))
    w /= w.sum()
    p = np.zeros(M)
    p[0] = 1.0
    idx = np.arange(M, dtype=np.int64)
    for _ in range(d):
        base = (3 * idx + 1) % M
        q = np.zeros(M)
        cur = base
        for a in range(AMAX):
            cur = (cur * inv2) % M
            q += w[a] * np.bincount(cur, weights=p, minlength=M)
        p = q
    return p


def check_identity(m: int, k: int) -> float:
    Ms = [3 ** d for d in range(m + 1)]
    V = []
    for d in range(m + 1):
        p = dist_X(d)
        V.append(np.conj(np.fft.fft(p)) if d > 0 else np.array([1.0 + 0j]))
    # 直接値
    xi = pow(2, k, Ms[m])
    G_direct = V[m][xi]
    # 分解値
    x = 2.0 ** k / Ms[m]
    wgt = [2.0 ** -a for a in range(1, AMAX + 1)]
    amp = {0: 1.0 + 0j}   # A -> E[e(xY_j);A_j=A]
    total = 0j
    P_good_phase = None
    for j in range(m):
        # 越境項: 状態 (j, A) から a > k-A
        for A, c in amp.items():
            d = m - j
            r = k - A
            F = 0j
            inv2d = pow(2, -1, Ms[d])
            for a in range(r + 1, r + AMAX + 1):
                e_mod = pow(inv2d, a - r, Ms[d]) if a > r else pow(2, r - a, Ms[d])
                ph = np.exp(2j * np.pi * e_mod / Ms[d])
                if d - 1 == 0:
                    Vv = 1.0 + 0j
                else:
                    Vv = V[d - 1][e_mod % Ms[d - 1]]
                F += (2.0 ** -a) * ph * Vv
            total += c * F
        # 前進 (A + a <= k のみ)
        nxt = {}
        for A, c in amp.items():
            for a in range(1, min(AMAX, k - A) + 1):
                A2 = A + a
                phase = np.exp(2j * np.pi * (x * 3 ** j * 2.0 ** -A2))
                nxt[A2] = nxt.get(A2, 0j) + c * wgt[a - 1] * phase
        amp = nxt
    good = sum(amp.values())
    total += good
    # no-positivity データ
    P_good = 0.0
    # P(A_m<=k) を別 DP で
    pa = {0: 1.0}
    for _ in range(m):
        nx = {}
        for A, pr in pa.items():
            for a in range(1, min(AMAX, k - A) + 1):
                nx[A + a] = nx.get(A + a, 0.0) + pr * wgt[a - 1]
        pa = nx
    P_good = sum(pa.values())
    rel = abs(total - G_direct) / abs(G_direct)
    print(f"  m={m}, k={k}: |G_direct|={abs(G_direct):.6f}  分解値との相対差 {rel:.2e}")
    print(f"    good項 E[e(xY);A_m<=k] = {good:.4f} (|.|={abs(good):.4f})"
          f"  vs P(A_m<=k) = {P_good:.4f}  → 位相損失比 {abs(good)/P_good:.3f}")
    return rel


# ---------- (B) ----------
def stable_log2c(K: int):
    """log₂c(k) (k=1..K) と Sturmian 文字 σ_j を返す。"""
    maxd = int(0.372 * K) + 8
    v = np.zeros(maxd)
    v[0] = 1.0
    logs = [0.0, 0.0]  # log2 c(1) = 0
    sigmas = [0]
    T2, T3, e = 2, 3, 0   # 2^j (j=1), 3^{e+1}
    offset = 0.0
    for j in range(1, K):
        T2 *= 2
        if T3 <= T2:
            sigma, e = 1, e + 1
            T3 *= 3
        else:
            sigma = 0
        sigmas.append(sigma)
        if sigma == 0:
            v = np.concatenate([[0.0], v[:-1]]) + v  # d→d+1 と d→d
        else:
            nv = v.copy()          # b=1: d→d
            nv[:-1] += v[1:]       # b=0: d→d-1
            v = nv
        s = v.sum()
        offset += math.log2(s)
        v /= s
        logs.append(offset)
    return np.array(logs), np.array(sigmas)


if __name__ == "__main__":
    print("(A) 第一通過繰り込み等式の検証")
    for (m, k) in [(6, 9), (7, 10), (8, 12)]:
        rel = check_identity(m, k)
        assert rel < 1e-8
    print("  等式成立 (L-δ2 の核となる正確な繰り込み等式が確定)\n")

    print("(B) Ostrowski 繰り込みの定量化")
    K = 30000
    logs, sigmas = stable_log2c(K)
    from certtree import climbing_counts_dp
    c_exact = climbing_counts_dp(400)
    for k in (10, 50, 100, 200, 400):
        rel = abs(logs[k] - math.log2(c_exact[k])) / math.log2(c_exact[k])
        assert rel < 1e-9, (k, rel)
    print(f"  安定化 DP: k<=400 で厳密値と一致 (<1e-9)、k<= {K} まで計算")
    phi = logs[1:K + 1] - H * np.arange(1, K + 1)
    dphi = np.diff(phi)
    sig = sigmas[1:len(dphi) + 1].astype(float)
    m0 = dphi[sig == 0].mean()
    m1 = dphi[sig == 1].mean()
    pred = np.where(sig == 0, m0, m1)
    ss_res = ((dphi - pred) ** 2).sum()
    ss_tot = ((dphi - dphi.mean()) ** 2).sum()
    r2 = 1 - ss_res / ss_tot
    print(f"  Δφ の Sturmian 文字回帰: E[Δφ|σ=0]={m0:+.5f}, E[Δφ|σ=1]={m1:+.5f}, R²={r2:.4f}")
    # 残差積算と不一致度の相関
    resid = np.cumsum(dphi - pred)
    js = np.arange(1, len(resid) + 1)
    frac = (js * THETA) % 1.0
    D = np.cumsum(frac - 0.5)
    r = np.corrcoef(resid, D[:len(resid)])[0, 1]
    print(f"  残差積算 vs 不一致度 D(k)=Σ({{jθ}}-1/2): Pearson r = {r:+.4f}")
    # 収束分母スケール
    print("  φ(k) = log₂c(k) − Hk at 収束分母 (log₃2 の q_n):")
    for q in (2, 3, 8, 19, 65, 84, 485, 1971, 4076, 24727):
        if q <= K:
            print(f"    q={q:6d}: φ = {phi[q - 1]:+.4f}")
