"""exp10_discriminate.py — δ_m 漸近機構の判別実験。

(A) 格子再帰を m <= 200 へ拡張 (float64; 絶対誤差 ~1e-14 << δ_200 ~ 4e-8)。
    k*(m)/m の極限 (3/2 か log₂3 か) と局所レート s_m の m 依存を測る。
    H1 (厳密定数): s_m ≡ log₂3 − 3/2 = 0.08496 bits (0.05889 nats)、補正 1/m。
    H2 (survival–位相均衡): s_m = I(log₂3) + c₁/√m + …、I_bits(log₂3)
       = (1−c)log₂(c/(2(c−1))) + 1 − log₂c |_{c=log₂3} ≈ 0.0793 bits へ低下。

(B) 有効模型の重点サンプリング検証: x_t = 2^{k−A_t}/3^{m−t+1},
    G_model = E[Π e(x_t); 0 ≤ k−A_t, x_t ≤ 1] を傾き k/m に指数傾斜した測度で推定し、
    真の δ_m と水準・傾きを比較する (機構検証)。
"""
import cmath
import math

import numpy as np

AMAX = 64
KLO = -96
LN2, LN3 = math.log(2), math.log(3)


def lattice(M_TOP=200):
    KHI = int(1.66 * M_TOP) + 30
    ks = list(range(KLO, KHI + 1))
    g_prev = {k: 1.0 + 0j for k in ks}
    weights = [2.0 ** -a for a in range(1, AMAX + 1)]
    out = {}
    for m in range(1, M_TOP + 1):
        M3 = 3 ** m
        inv2 = pow(2, -1, M3)
        pw = {}
        v = pow(inv2, -(KLO - AMAX), M3)
        pw[KLO - AMAX] = v
        for j in range(KLO - AMAX + 1, KHI + 1):
            v = (v * 2) % M3
            pw[j] = v
        g_cur = {}
        for k in ks:
            s = 0j
            for a in range(1, AMAX + 1):
                ka = k - a
                if ka < KLO:
                    break
                s += weights[a - 1] * cmath.exp(2j * math.pi * pw[ka] / M3) * g_prev[ka]
            g_cur[k] = s
        g_prev = g_cur
        kstar = max((k for k in ks if k >= 0), key=lambda k: abs(g_cur[k]))
        out[m] = (kstar, abs(g_cur[kstar]))
    return out


def I_bits(c):
    return (1 - c) * math.log2(c / (2 * (c - 1))) + 1 - math.log2(c)


def model_mc(m, k, N=200_000, chunk=50_000, seed=1):
    """傾斜測度での有効模型推定。返り値 |G_model|。"""
    c = k / m
    # 傾斜 s: 傾斜幾何分布の平均 = c
    lo, hi = -3.0, LN2 - 1e-9

    def mean_tilt(s):
        a = np.arange(1, AMAX + 1, dtype=float)
        w = 2.0 ** -a * np.exp(s * a)
        return (a * w).sum() / w.sum()

    for _ in range(80):
        mid = (lo + hi) / 2
        if mean_tilt(mid) < c:
            lo = mid
        else:
            hi = mid
    s = (lo + hi) / 2
    a_vals = np.arange(1, AMAX + 1, dtype=float)
    w = 2.0 ** -a_vals * np.exp(s * a_vals)
    Z = w.sum()
    probs = w / Z
    rng = np.random.default_rng(seed)
    total = 0j
    n_done = 0
    while n_done < N:
        n = min(chunk, N - n_done)
        a = rng.choice(np.arange(1, AMAX + 1), size=(n, m), p=probs)
        A = np.cumsum(a, axis=1)
        ex = k - A                       # k - A_t, t=1..m
        depth = m - np.arange(1, m + 1) + 1  # m-t+1
        y = ex * LN2 - depth * LN3       # ln x_t
        valid = ((ex >= 0) & (y <= 0)).all(axis=1)
        yv = np.where(y > -45, y, -np.inf)
        x = np.exp(yv, where=yv > -np.inf, out=np.zeros_like(yv))
        phi = 2 * np.pi * x.sum(axis=1)
        lw = -s * A[:, -1] + m * math.log(Z)
        contrib = np.where(valid, np.exp(lw), 0.0) * np.exp(1j * phi)
        total += contrib.sum()
        n_done += n
    return abs(total / N), s


if __name__ == "__main__":
    print("=== (A) 格子再帰 m<=200 ===")
    out = lattice(200)
    print("m, δ_m, k*, k*/m, 局所レート s_m (nats, 1/m 補正済):")
    ms_show = [60, 80, 100, 120, 140, 160, 180, 200]
    for m in ms_show:
        k, d = out[m]
        m2 = m - 20
        k2, d2 = out[m2]
        s_local = -(math.log(d) - math.log(d2)) / 20 - (math.log(m) - math.log(m2)) / 20
        print(f"  m={m:3d}: δ={d:.4e}  k*={k}  k*/m={k/m:.4f}  s_m={s_local:.5f}")
    I0 = I_bits(math.log2(3)) * LN2  # nats
    print(f"\n判別基準: H1 定数 = {LN3 - 1.5*LN2:.5f} nats,  "
          f"H2 極限 I(log₂3) = {I0:.5f} nats")
    print(f"I_bits(3/2) = {I_bits(1.5):.5f} = 5/2 − (3/2)log₂3 = {2.5-1.5*math.log2(3):.5f} (検算)")

    # z 検定: H1: lnδ + (log3−1.5log2)m + ln m = const
    #         H2: lnδ + I0·m + c1√m + β ln m = const (c1, β 最小二乗)
    ms = np.array([m for m in range(60, 201, 10)], dtype=float)
    ys = np.array([math.log(out[int(m)][1]) for m in ms])
    z1 = ys + (LN3 - 1.5 * LN2) * ms + np.log(ms)
    print("\nH1 z-検定 (定数なら合格): ", " ".join(f"{z:+.3f}" for z in z1))
    X = np.vstack([np.sqrt(ms), np.log(ms), np.ones_like(ms)]).T
    yy = ys + I0 * ms
    coef, res_, *_ = np.linalg.lstsq(X, -yy, rcond=None)
    pred = -(X @ coef)
    rss2 = float(((pred - yy) ** 2).sum())
    rss1 = float(((z1 - z1.mean()) ** 2).sum())
    print(f"H1 残差二乗和 (定数モデル): {rss1:.4f}")
    print(f"H2 lnδ = −I0·m − {coef[0]:.4f}√m − {coef[1]:.4f}ln m − {coef[2]:.4f}: RSS={rss2:.4f}")

    print("\n=== (B) 有効模型 (survival–位相) の直接推定 ===")
    print("m, k*, |G_model|, δ_true, 比:")
    for m in (40, 80, 120, 160, 200):
        k, d_true = out[m]
        g_mod, s = model_mc(m, k, N=200_000)
        print(f"  m={m:3d}: k*={k}  |G_model|={g_mod:.4e}  δ_true={d_true:.4e}  "
              f"model/true={g_mod/d_true:.3f}  (tilt s={s:+.4f})")
