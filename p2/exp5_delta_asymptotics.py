"""exp5_delta_asymptotics.py — δ_m (Syracuse 3進 Fourier 減衰) の漸近混合率の確定。

構造事実(証明済み・コードで利用):
  (1) 連鎖は m ステップで厳密に定常: W_m mod 3^m は W_0 に依存しない。
      ⇒ 反復は m 回で厳密(打ち切り誤差は幾何分布の裾 2^-AMAX のみ)。
  (2) f_m(ξ) = Σ_a 2^{-a} e(ξ 2^{-a}/3^m) f_{m-1}(ξ 2^{-a} mod 3^{m-1})
      ⇒ |f_m| ≤ max|f_{m-1}| なので δ_m ≤ δ_{m-1} (単調減少は定理)。

計画:
  Phase 1: m ≤ M_DENSE で π_m を厳密計算 (bincount)、FFT で δ_m と argmax ξ*_m、
           L2 平坦度 R_m = 3^m Σπ² を出す。ξ*_m の 3 進持ち上げ構造を検査。
  Phase 2: m = M_DENSE+1..19 で、ξ*_{M_DENSE} の 3 進持ち上げ候補上の f を
           モンテカルロ推定 (N サンプル) し、δ_m 系列を延長。
           (妥当性検証: m = M_DENSE で MC値 vs 厳密値を比較)
  Phase 3: 減衰モデル比較: log δ_m ~ α m / α m + β log m / α √m。
"""
import math
import numpy as np

AMAX = 60
M_DENSE = 15
M_MC = 19
N_MC = 10 ** 7
rng = np.random.default_rng(20260814)


def dense_delta(m: int):
    M = 3 ** m
    inv2 = pow(2, -1, M)
    w = 2.0 ** -(np.arange(1, AMAX + 1))
    w /= w.sum()
    p = np.zeros(M)
    p[0] = 1.0
    idx = np.arange(M, dtype=np.int64)
    for _ in range(m):
        base = (3 * idx + 1) % M
        q = np.zeros(M)
        cur = base
        for a in range(AMAX):
            cur = (cur * inv2) % M
            q += w[a] * np.bincount(cur, weights=p, minlength=M)
        p = q
    ph = np.fft.fft(p)
    xi = np.arange(M)
    mask = (xi % 3 != 0)
    mags = np.abs(ph)
    mags[~mask] = 0
    ximax = int(np.argmax(mags))
    delta = float(mags[ximax])
    R = float(M * np.sum(p * p))
    # 上位周波数 (平衡表現)
    top = np.argsort(mags)[-6:][::-1]
    top_bal = [int(t) if t <= M // 2 else int(t) - M for t in top]
    return delta, ximax, R, top_bal, mags


def mc_f(m: int, xis, N: int):
    """f_m(ξ) = E e(ξ X/3^m), X = Σ_{i=1..m} 3^{i-1} 2^{-A_i} を MC 推定。"""
    M = 3 ** m
    inv2 = pow(2, -1, M)
    max_a_total = AMAX * m
    pow_inv2 = np.empty(max_a_total + 1, dtype=np.int64)
    v = 1
    for k in range(max_a_total + 1):
        pow_inv2[k] = v
        v = (v * inv2) % M
    # 幾何分布サンプル (1 + Geom): a = 1 + floor(log2(1/U)) 相当
    a = rng.geometric(0.5, size=(N, m)).astype(np.int64)
    np.clip(a, 1, AMAX, out=a)
    A = np.cumsum(a, axis=1)
    X = np.zeros(N, dtype=np.int64)
    p3 = 1
    for i in range(m):
        X = (X + p3 * pow_inv2[A[:, i]]) % M
        p3 = (p3 * 3) % M
    out = {}
    for xi in xis:
        ph = ((xi % M) * X) % M
        z = np.exp(2j * np.pi * ph / M)
        out[xi] = complex(z.mean())
    return out


if __name__ == "__main__":
    print("Phase 1: 厳密計算 (m <= %d)" % M_DENSE)
    deltas = {}
    argmaxes = {}
    prev = None
    for m in range(1, M_DENSE + 1):
        delta, ximax, R, top_bal, _ = dense_delta(m)
        deltas[m] = delta
        argmaxes[m] = ximax
        ratio = delta / prev if prev else float("nan")
        print(f"  m={m:2d}: δ={delta:.6e}  ratio={ratio:.4f}  R_m={R:.4f}  "
              f"top|ξ|(平衡)={top_bal[:3]}")
        prev = delta
    # argmax の持ち上げ構造: ξ*_m mod 3^(m-1) が ±2^j ξ*_(m-1) の軌道に入るか
    print("\n  argmax 持ち上げ検査 (ξ*_m mod 3^(m-1) ∈ ±2^Z·ξ*_(m-1)?):")
    for m in range(3, M_DENSE + 1):
        Mp = 3 ** (m - 1)
        t = argmaxes[m] % Mp
        s = argmaxes[m - 1] % Mp
        ok = False
        cur = s
        for _ in range(2 * 3 ** (m - 2)):
            if cur == t or Mp - cur == t:
                ok = True
                break
            cur = (cur * 2) % Mp
        print(f"    m={m:2d}: {'YES' if ok else 'NO'}")

    print("\nPhase 2: MC 延長 (持ち上げ候補上, N=%.0e)" % N_MC)
    # 妥当性検証: m=M_DENSE の argmax で MC vs 厳密
    val = mc_f(M_DENSE, [argmaxes[M_DENSE]], N_MC)
    print(f"  検証 m={M_DENSE}: MC |f|={abs(val[argmaxes[M_DENSE]]):.5f} "
          f"vs 厳密 {deltas[M_DENSE]:.5f}")
    cand = [argmaxes[M_DENSE]]
    for m in range(M_DENSE + 1, M_MC + 1):
        M = 3 ** m
        Mp = 3 ** (m - 1)
        lifts = []
        for c in cand:
            for k in range(3):
                lifts.append((c + k * Mp) % M)
                lifts.append((-(c + k * Mp)) % M)
        lifts = [x for x in set(lifts) if x % 3 != 0]
        res = mc_f(m, lifts, N_MC)
        best = max(res, key=lambda x: abs(res[x]))
        deltas[m] = abs(res[best])
        print(f"  m={m:2d}: δ>=|f|max={deltas[m]:.5f}  ratio={deltas[m]/deltas[m-1]:.4f}  "
              f"(候補 {len(lifts)} 個)")
        # 次段の種: 上位3候補
        cand = sorted(res, key=lambda x: -abs(res[x]))[:3]

    print("\nPhase 3: モデル判別 (テール m=8..%d)" % M_MC)
    ms = np.array(sorted(k for k in deltas if k >= 8), dtype=float)
    ys = np.array([math.log(deltas[int(k)]) for k in ms])
    for name, X in [
        ("純指数  log δ = α m + c", np.vstack([ms, np.ones_like(ms)]).T),
        ("指数+冪 log δ = α m + β ln m + c",
         np.vstack([ms, np.log(ms), np.ones_like(ms)]).T),
        ("伸長指数 log δ = α √m + c", np.vstack([np.sqrt(ms), np.ones_like(ms)]).T),
    ]:
        coef, res_, *_ = np.linalg.lstsq(X, ys, rcond=None)
        rss = float(res_[0]) if len(res_) else float(np.sum((X @ coef - ys) ** 2))
        out = ", ".join(f"{c:+.4f}" for c in coef)
        print(f"  {name}: [{out}]  RSS={rss:.2e}")
        if name.startswith("純指数"):
            print(f"    ⇒ ρ = e^α = {math.exp(coef[0]):.4f} "
                  f"(参考: 2^(-1/3)={2**(-1/3):.4f}, 3^(-1/5)={3**(-0.2):.4f}, "
                  f"4/5=0.8000, 5/6=0.8333)")
