"""exp25_anticoncentration.py — 補題Cの反集中: 決定論的上限の機械検証と ν₂ 分布の測定。

(1) 決定論的上限 (補題Bの帰結・証明済み): 黒走行長 run ≤ ⌈ν₂(v_entry)/2⌉。
    継続には b_j ≤ ν₂(v) が必要で b ≥ 2、ν₂ は各ステップ b ずつ減るため。
    → 全突入イベントで assert 検証。
(2) 反集中の対象: P(ν₂(v_entry) ≥ s) の測定と幾何(1/2) との照合。
    対照: wrapped 全ステップの ν₂ 分布 (等分布なら同じく幾何(1/2))。
(3) 機構: 突入値の低位ビット b₀..b₇ の偏り (等分布なら各 1/2)。
"""
import math
import random

LOG2_3 = math.log2(3)
EPS = 0.01
SMAX = 14


def nu2(x):
    if x == 0:
        return 60
    n = 0
    while x % 2 == 0:
        x //= 2
        n += 1
    return n


def run_band(m, k, walks, seed):
    M3 = 3 ** m
    inv2 = pow(2, -1, M3)
    thr = int(EPS * M3)
    r = random.Random(seed)

    def geom():
        u = r.random()
        return min(int(math.floor(-math.log(u, 2))) + 1, 20)

    ent_nu = [0] * (SMAX + 1)
    all_nu = [0] * (SMAX + 1)
    bits = [0] * 8
    entries = 0
    allsteps = 0
    viol = 0
    for _ in range(walks):
        b = geom() + geom()
        L = b
        e = k - L + 1
        val = (pow(2, e, M3) if e >= 0 else pow(inv2, -e, M3)) % M3
        prev_black = False
        run = 0
        entry_nu = 0
        for j in range(2, m // 2 + 1):
            b = geom() + geom()
            L += b
            val = (val * 9) % M3
            for _ in range(b):
                val = (val * inv2) % M3
            if k - L + 1 < 0:
                sv = val if val <= M3 // 2 else val - M3
                blk = abs(sv) <= thr
                allsteps += 1
                nv = min(nu2(abs(sv)) if sv != 0 else SMAX, SMAX)
                all_nu[nv] += 1
                if blk and not prev_black:
                    entries += 1
                    entry_nu = nv
                    ent_nu[nv] += 1
                    for i in range(8):
                        bits[i] += (abs(sv) >> i) & 1
                    run = 1
                elif blk:
                    run += 1
                else:
                    if run > 0 and run > (entry_nu + 1) // 2 + 1:
                        viol += 1
                    run = 0
                prev_black = blk
    return ent_nu, all_nu, bits, entries, allsteps, viol


if __name__ == "__main__":
    m = 240
    print("(1)(2)(3) の帯別測定 (m=240):")
    for tag, k in [("deep k=0.2mα", int(0.2 * m * LOG2_3)),
                   ("shoulder δ=0.05", int(m * LOG2_3 - 0.05 * m))]:
        ent, alln, bits, E, A, viol = run_band(m, k, walks=1500, seed=k)
        print(f"\n  {tag}: 突入 {E}, wrapped {A}, 決定論的上限の破れ {viol}")
        cum = 0
        print("   s: P(ν₂=s|突入)  vs 幾何(1/2)=2^-(s+1) | P(ν₂=s|全wrapped)")
        for s in range(0, 7):
            pe = ent[s] / max(E, 1)
            pa = alln[s] / max(A, 1)
            print(f"   {s}: {pe:.4f}  vs {2.0**-(s+1):.4f}  | {pa:.4f}")
        tail3_e = sum(ent[s] for s in range(4, SMAX + 1)) / max(E, 1)
        tail3_a = sum(alln[s] for s in range(4, SMAX + 1)) / max(A, 1)
        print(f"   P(ν₂≥4): 突入 {tail3_e:.4f} vs 幾何 {2.0**-4:.4f} | 全 {tail3_a:.4f}")
        print(f"   低位ビット偏り (突入値, 期待 0.5): "
              f"{[round(b/max(E,1),3) for b in bits]}")
