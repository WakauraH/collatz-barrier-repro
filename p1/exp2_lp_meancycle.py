"""exp2_lp_meancycle.py — パネル実験(ii): シンドローム重み付き Lyapunov LP (深さ d) の
実行可能性を最大平均サイクルへ厳密帰着して検査し、Farkas 双対(=最悪サイクル)の台を同定する。

帰着: phi(n) = log2(n) + psi(n mod 2^d) が全 n>1 で phi(Tc n) <= phi(n) - eps
  ⟺ 差分制約系 psi(succ) - psi(state) <= -eps - drift(class)  (類 = 剰余 mod 2^{d+1})
  ⟺ シンドローム遷移グラフ(状態 2^d 個、各状態から 2 本)の全サイクルの平均 drift <= -eps
  ⟺ max mean cycle drift < 0  (最良の eps = -max mean)

drift の有理数囲い込み:
  偶類: drift = -1 (厳密)
  奇類: drift ∈ [L15, U15 + 1/(3 m ln2)]  (m = 類の最小元 >= 3, L15/U15 は log2(3/2) の
        10^15 スケール整数囲い込み; 上側は切上げ、下側は切下げ)
結論の向き: 下側重みでも max mean > 0 なら真の系も非実行可能(厳密)。

追加実験: trailing-ones(r) >= j の状態を削除した制限グラフの max mean = -mu_j。
mu_j > 0 なら「高 trailing-ones 類を避ける軌道には一様降下 Lyapunov が存在する」ことになり、
非降下軌道の高 trailing-ones 類への訪問頻度下界 f >= mu_j/(mu_j + Dmax) が従う。

Karp の最大平均サイクル: F[k][v] = k 辺経路の最大重み。mu* = max_v min_k (F[n][v]-F[k][v])/(n-k)。
整数演算(10^15 スケール)。
"""
import math
from decimal import Decimal, getcontext

import numpy as np

getcontext().prec = 50
SCALE = 10 ** 15
NEG = -(10 ** 17)  # -inf sentinel

# log2(3/2) の囲い込み (Decimal 50桁 -> 10^15 整数)
_l15 = Decimal(3).ln() / Decimal(2).ln() - 1  # log2(3/2) = log2 3 - 1
L15 = int((_l15 * SCALE).to_integral_value(rounding="ROUND_FLOOR"))
U15 = int((_l15 * SCALE).to_integral_value(rounding="ROUND_CEILING"))
_inv_ln2 = 1 / Decimal(2).ln()


def build_edges(d: int, upper: bool):
    """返り値: (src, dst, w) 配列。状態 = r mod 2^d。lift rr in {r, r+2^d} mod 2^{d+1}。"""
    D, D2 = 1 << d, 1 << (d + 1)
    src, dst, w = [], [], []
    for r in range(D):
        for rr in (r, r + D):
            if r % 2 == 0:
                s2 = (rr // 2) % D
                wt = -1 * SCALE
            else:
                s2 = ((3 * rr + 1) // 2) % D
                m = rr if rr >= 3 else rr + D2  # 類の最小元 (n=1 を除外)
                if upper:
                    corr = int((_inv_ln2 / (3 * m) * SCALE).to_integral_value(
                        rounding="ROUND_CEILING"))
                    wt = U15 + corr
                else:
                    wt = L15
            src.append(r)
            dst.append(s2)
            w.append(wt)
    return np.array(src), np.array(dst), np.array(w, dtype=np.int64)


def max_mean_cycle(d: int, src, dst, w, alive_mask=None):
    """Karp。alive_mask: 使用可能状態の bool 配列 (None = 全状態)。
    返り値: (mu*_scaled_float, argmax 状態) — mu* は SCALE 単位の有理値を float 表示。"""
    D = 1 << d
    if alive_mask is not None:
        keep = alive_mask[src] & alive_mask[dst]
        src, dst, w = src[keep], dst[keep], w[keep]
        if len(src) == 0:
            return None, None
    n = int(alive_mask.sum()) if alive_mask is not None else D
    F = np.full((n + 1, D), NEG, dtype=np.int64)
    start = alive_mask.nonzero()[0] if alive_mask is not None else np.arange(D)
    F[0][start] = 0
    for k in range(1, n + 1):
        nxt = np.full(D, NEG, dtype=np.int64)
        cand = F[k - 1][src] + w
        cand[F[k - 1][src] <= NEG // 2] = NEG
        np.maximum.at(nxt, dst, cand)
        F[k] = nxt
    best_mu, best_v = None, None
    Fn = F[n]
    for v in range(D):
        if Fn[v] <= NEG // 2:
            continue
        vals = [(Fn[v] - F[k][v]) / (n - k) for k in range(n) if F[k][v] > NEG // 2]
        if not vals:
            continue
        mu_v = min(vals)
        if best_mu is None or mu_v > best_mu:
            best_mu, best_v = mu_v, v
    return (best_mu / SCALE if best_mu is not None else None), best_v


def trailing_ones(r: int, d: int) -> int:
    t = 0
    while t < d and (r >> t) & 1:
        t += 1
    return t


if __name__ == "__main__":
    print(f"log2(3/2) 囲い込み: [{L15}/{SCALE}, {U15}/{SCALE}]")
    for d in (4, 6, 8, 10):
        src, dst, w_up = build_edges(d, upper=True)
        _, _, w_lo = build_edges(d, upper=False)
        mu_up, v_up = max_mean_cycle(d, src, dst, w_up)
        mu_lo, v_lo = max_mean_cycle(d, src, dst, w_lo)
        allones = (1 << d) - 1
        print(f"\nd={d}: 全グラフ max mean cycle: 上側重み {mu_up:+.6f} (argmax 状態 {v_up}), "
              f"下側重み {mu_lo:+.6f}")
        print(f"  全1状態 r={allones} の自己ループ重み(下側) = {L15/SCALE:+.6f}"
              f" -> 下側でも正 ⇒ 深さ {d} の LP は厳密に非実行可能")
        assert mu_lo > 0
        # 制限グラフ: trailing-ones >= j の状態を削除
        t_arr = np.array([trailing_ones(r, d) for r in range(1 << d)])
        print(f"  制限グラフ (trailing-ones >= j を削除, 上側重み=保守的):")
        for j in range(d, 0, -1):
            alive = t_arr < j
            mu_j, v_j = max_mean_cycle(d, src, dst, w_up, alive)
            if mu_j is None:
                print(f"    j={j:2d}: サイクルなし")
                continue
            if mu_j <= 0:
                dmax = U15 / SCALE + 1 / (9 * math.log(2))  # 奇ステップ drift の粗い上限
                f_lb = (-mu_j) / ((-mu_j) + dmax)
                print(f"    j={j:2d}: mu={mu_j:+.6f} 負 ⇒ 制限グラフに Lyapunov 存在; "
                      f"非降下軌道の trailing-ones>={j} 訪問頻度 >= {f_lb:.4f}")
            else:
                print(f"    j={j:2d}: mu={mu_j:+.6f} 正 (障害残存, argmax 状態 {v_j:b})")
