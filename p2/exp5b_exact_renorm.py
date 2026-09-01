"""exp5b_exact_renorm.py — δ_m の漸近率: 2冪周波数上の厳密繰り込み再帰。

観測事実 (exp5 Phase1, m<=15 の全周波数厳密計算): argmax は常に ξ = ±2^k,
k(m) は増分パターン (2,1,1) で k ≈ 4m/3。そこで 2冪周波数に制限した
    g_m(k) := f_m(2^k mod 3^m),   f_m(ξ) = E e(ξ X / 3^m)
の厳密再帰
    g_m(k) = Σ_{a>=1} 2^{-a} e(2^{k-a} mod 3^m / 3^m) · g_{m-1}(k-a),  g_0 ≡ 1
を k ∈ [KLO, KHI] で m=60 まで計算する。
  - a は AMAX で打ち切り (誤差 <= m·2^{-AMAX})
  - k-a < KLO の寄与は 0 と置く (誤差 <= 2^{-(k-KLO)}; 対象 k >= 0 で無視可能)
  - 2^j mod 3^m は負冪も含め厳密 (pow / modinv)
δ_m^{(2)} := max_k |g_m(k)| は δ_m の下界であり、m<=15 では全周波数厳密値と一致する
ことを検証する (argmax が 2冪であることの再確認)。

出力: δ_m^{(2)}, argmax k*(m), 比 δ_m/δ_{m-1}, 3期幾何平均比, k*(m) 増分列,
モデル当てはめ (純指数 / 指数+冪 / 伸長指数)。
"""
import math
import cmath
import numpy as np

AMAX = 64
KLO = -96
M_TOP = 60

# exp5 の全周波数厳密値 (検証用)
DENSE = {1: 5.773503e-01, 2: 3.779236e-01, 3: 2.522368e-01, 4: 1.769989e-01,
         5: 1.292736e-01, 6: 9.610639e-02, 7: 7.587004e-02, 8: 6.089074e-02,
         9: 4.802615e-02, 10: 3.827832e-02, 11: 3.194419e-02, 12: 2.645817e-02,
         13: 2.205243e-02, 14: 1.912799e-02, 15: 1.628448e-02}

if __name__ == "__main__":
    KHI = int(1.75 * M_TOP) + 8
    ks = list(range(KLO, KHI + 1))
    idx = {k: i for i, k in enumerate(ks)}
    g_prev = {k: 1.0 + 0j for k in ks}          # g_0
    weights = [2.0 ** -a for a in range(1, AMAX + 1)]

    deltas, kstars = {}, {}
    for m in range(1, M_TOP + 1):
        M3 = 3 ** m
        inv2 = pow(2, -1, M3)
        # 2^j mod 3^m for j in [KLO-AMAX, KHI]
        pw = {}
        v = pow(inv2, -(KLO - AMAX), M3) if KLO - AMAX < 0 else pow(2, KLO - AMAX, M3)
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
                    break  # 寄与を 0 と置く (誤差 <= 2^-(k-KLO))
                s += weights[a - 1] * cmath.exp(2j * math.pi * pw[ka] / M3) * g_prev[ka]
            g_cur[k] = s
        g_prev = g_cur
        kstar = max(ks, key=lambda k: abs(g_cur[k]))
        deltas[m] = abs(g_cur[kstar])
        kstars[m] = kstar

    print("m, δ_m^(2), ratio, k*(m), Δk, dense一致")
    prev = None
    for m in range(1, M_TOP + 1):
        r = deltas[m] / prev if prev else float("nan")
        dk = kstars[m] - kstars[m - 1] if m > 1 else 0
        chk = ""
        if m in DENSE:
            rel = abs(deltas[m] - DENSE[m]) / DENSE[m]
            chk = f"dense比 {rel:.1e}"
        print(f"  {m:2d}  {deltas[m]:.6e}  {r:.4f}  k*={kstars[m]:3d}  Δk={dk}  {chk}")
        prev = deltas[m]

    print("\n3期幾何平均比 (δ_(m)/δ_(m-3))^(1/3):")
    for m in range(6, M_TOP + 1, 3):
        r3 = (deltas[m] / deltas[m - 3]) ** (1 / 3)
        print(f"  m={m:2d}: {r3:.5f}")

    print(f"\nk*(m)/m -> {kstars[M_TOP]/M_TOP:.4f}  (4/3={4/3:.4f}, log2 3={math.log2(3):.4f})")

    ms = np.array(range(24, M_TOP + 1), dtype=float)
    ys = np.array([math.log(deltas[int(k)]) for k in ms])
    print("\nモデル当てはめ (m=24..%d):" % M_TOP)
    for name, X in [
        ("純指数  αm+c        ", np.vstack([ms, np.ones_like(ms)]).T),
        ("指数+冪 αm+β·ln m+c ", np.vstack([ms, np.log(ms), np.ones_like(ms)]).T),
        ("伸長    α√m+c       ", np.vstack([np.sqrt(ms), np.ones_like(ms)]).T),
    ]:
        coef, res_, *_ = np.linalg.lstsq(X, ys, rcond=None)
        pred = X @ coef
        rss = float(np.sum((pred - ys) ** 2))
        print(f"  {name}: {[f'{c:+.5f}' for c in coef]}  RSS={rss:.3e}")
        if name.startswith("純指数"):
            rho = math.exp(coef[0])
            print(f"    ρ = {rho:.5f}   参考: 2^(-1/3)={2**(-1/3):.5f}, "
                  f"3^(-1/5)={3**(-.2):.5f}, (4/3を使う説) 2^(-4/3)·3={2**(-4/3)*3:.5f}")
