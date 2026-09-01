"""exp4_syracuse_mixing.py — (β) Tao 型輸送の実効化: Syracuse 連鎖の 3 進混合率の厳密計算
と、例外軌道の決定論的 KL 異常率補題の数値検証。

Part A (Syracuse 3進混合):
  U 軌道の mod 3^m 残差は Markov 連鎖 w ↦ (3w+1)·2^{-a} mod 3^m (a ~ Geom(1/2)) に従い、
  m ステップ後には初期値に依存しない (n_m ≡ β_m 2^{-A_m} mod 3^m)。
  この連鎖の定常分布 π_m を計算し、非自明指標での最大 Fourier 係数
      δ_m = max_{3∤ξ} |π̂_m(ξ)|
  を求める。δ_m の減衰率 ρ = δ_m^{1/m} が Tao (2022) の証明のエンジン
  (Syracuse random variable の 3 進 Fourier 減衰) の実効定数である。
  幾何分布は a <= AMAX で打ち切り (質量誤差 2^-AMAX)。

Part B (KL 異常率補題の恒等式検証):
  θ = log_3 2 として、決定論的補題
    「k ステップ非降下 U 窓の経験 a 分布 P̂ は E[P̂] <= log2 3 + o(1) を満たし、
     ゆえに D(P̂ ‖ Geom(1/2)) >= D(Geom(θ) ‖ Geom(1/2))」
  の率が 2 進側の例外密度指数と厳密に一致すること:
    θ · D(Geom(θ) ‖ Geom(1/2)) = 1 − H(θ)   [bits]
  を高精度で検証する (二つの時計 — U ステップと Tc ステップ — の換算恒等式)。
"""
import numpy as np
from decimal import Decimal, getcontext

getcontext().prec = 50
AMAX = 60


def syracuse_stationary(m: int, iters: int = 400):
    M = 3 ** m
    inv2 = pow((M + 1) // 2, 1, M)  # 2^{-1} mod 3^m
    # 遷移を先に添字配列で: T[a][w] = (3w+1)*inv2^a mod M
    w = np.arange(M, dtype=np.int64)
    base = (3 * w + 1) % M
    weights = np.array([2.0 ** -(a + 1) for a in range(AMAX)])
    weights /= weights.sum()
    maps = []
    cur = base.copy()
    for a in range(AMAX):
        cur = (cur * inv2) % M
        maps.append(cur.copy())
    p = np.full(M, 1.0 / M)
    for _ in range(iters):
        q = np.zeros(M)
        for a in range(AMAX):
            np.add.at(q, maps[a], weights[a] * p)
        p = q
    return p


def max_nontrivial_fourier(p):
    M = len(p)
    ph = np.fft.fft(p)
    xi = np.arange(M)
    mask = (xi % 3 != 0)
    return np.abs(ph[mask]).max()


if __name__ == "__main__":
    print("Part A: Syracuse 連鎖の 3 進混合 (δ_m = max_{3∤ξ}|π̂(ξ)|)")
    prev = None
    for m in range(1, 11):
        p = syracuse_stationary(m)
        d = max_nontrivial_fourier(p)
        rho = d ** (1 / m)
        ratio = (d / prev) if prev else float("nan")
        print(f"  m={m:2d}: δ_m = {d:.6e}   δ_m^(1/m) = {rho:.4f}   δ_m/δ_(m-1) = {ratio:.4f}")
        prev = d
    print("  (δ_m/δ_(m-1) の収束値が漸近混合率。3^(-1/2)=0.577, 1/2=0.5, 2/3=0.667 と比較せよ)\n")

    print("Part B: KL 異常率恒等式 θ·D(Geom(θ)‖Geom(1/2)) = 1 − H(θ)")
    theta = Decimal(2).ln() / Decimal(3).ln()
    ln2 = Decimal(2).ln()
    # D(Geom(p)‖Geom(q)) = ln(p/q) + (1/p − 1)·ln((1−p)/(1−q))  [nats]
    p_, q_ = theta, Decimal("0.5")
    D = (p_ / q_).ln() + (1 / p_ - 1) * ((1 - p_) / (1 - q_)).ln()
    lhs = theta * D / ln2  # bits
    H = -(p_ * (p_.ln() / ln2) + (1 - p_) * ((1 - p_).ln() / ln2))
    rhs = 1 - H
    print(f"  θ = {float(theta):.12f}")
    print(f"  D(Geom(θ)‖Geom(1/2)) = {float(D / ln2):.12f} bits/odd-step")
    print(f"  θ·D = {float(lhs):.15f}")
    print(f"  1−H(θ) = {float(rhs):.15f}")
    print(f"  差 = {float(abs(lhs - rhs)):.2e}  (一致 ⇒ 2進・3進の二つの時計の換算恒等式が成立)")
    assert abs(lhs - rhs) < Decimal(10) ** -30
