"""exp6_rigor_base.py — δ_m 漸近問題の厳密基盤の検証。

L-A (原始根): ord(2 mod 3^m) = 2·3^{m-1} (= |単元群|) を m <= 12 で検証。
  ⇒ すべての単元は 2 の冪。1次元指数再帰 g_m(j) は全周波数を尽くす(無仮定)。
L-B (局在検証): 稠密 FFT の argmax ξ*_m の離散対数 j = dlog_2(±ξ*_m) を計算し、
  j (mod 2·3^{m-1}) が小窓 [0, 2m] に入ること (argmax 指数の局在) を m <= 10 で確認。
L-C (ミニ障壁の定量): ridge 周波数 ξ = 2^{floor(3m/2)} では深さ t の再帰展開に現れる
  全位相が |phase-1| <= 2π·2^{k}/3^m · Σ… <= 2π·ρ^m 級であることを数値確認
  (有限レベル情報だけでは減衰が証明できないことの実測)。
"""
import cmath
import math

import numpy as np

from exp5_delta_asymptotics import dense_delta


def ord2(m: int) -> int:
    M = 3 ** m
    o, v = 1, 2
    while v != 1:
        v = (v * 2) % M
        o += 1
    return o


def dlog2(x: int, m: int) -> int:
    M = 3 ** m
    v, j = 1, 0
    while v != x:
        v = (v * 2) % M
        j += 1
        assert j <= 2 * 3 ** (m - 1)
    return j


if __name__ == "__main__":
    print("L-A: ord(2 mod 3^m) = 2·3^(m-1) = |単元群| (2 は原始根)")
    for m in range(1, 13):
        o = ord2(m)
        assert o == 2 * 3 ** (m - 1), (m, o)
    print("  m=1..12: OK — すべての単元 ξ は ξ = 2^j (mod 3^m)\n")

    print("L-B: 稠密 argmax の離散対数 (±ξ* = 2^j; j が小窓に局在するか)")
    for m in range(2, 11):
        delta, ximax, R, top_bal, mags = dense_delta(m)
        M = 3 ** m
        cands = []
        for sgn, x in (("+", ximax), ("-", (M - ximax) % M)):
            try:
                j = dlog2(x, m)
                cands.append((sgn, j))
            except AssertionError:
                pass
        best = min(cands, key=lambda t: t[1])
        window = best[1] <= 2 * m
        print(f"  m={m:2d}: ξ*={ximax}  ±2^j: {cands}  最小指数 {best[1]}"
              f"  小窓[0,{2*m}]内: {'YES' if window else 'NO'}")

    print("\nL-C: ridge 周波数での位相の消失 (有限レベル障壁)")
    for m in (20, 40, 60):
        k = int(1.5 * m)
        M = 3 ** m
        worst = 0.0
        for a in range(1, min(k, 61)):
            ph = abs(cmath.exp(2j * math.pi * pow(2, k - a, M) / M) - 1)
            worst = max(worst, ph)
        rho_m = (2 ** 1.5 / 3) ** m
        print(f"  m={m}: k=3m/2={k}, max_a<=60 |e(2^(k-a)/3^m)-1| = {worst:.3e}"
              f"  (~2π·ρ^m = {2*math.pi*rho_m:.3e})")
    print("  ⇒ ridge 上では有限個のレベルの位相情報は 1 と区別不能:")
    print("    有限レベル展開に基づくいかなる上界も因子 >= 1 - O(m·ρ^m) しか出せず、")
    print("    δ_m の指数減衰の証明には指数無限個のレベル (k の降下全体) が必要")
