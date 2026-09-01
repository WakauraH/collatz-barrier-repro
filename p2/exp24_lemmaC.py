"""exp24_lemmaC.py — 補題C(突入あたり捕捉時間 O(1)・幾何裾)の直接測定。

値連鎖: v_{j+1} = 9·v_j·inv2^{b_j} mod 3^m (符号付き剰余)、b_j ~ Pascal(2,1/2)。
黒 = |v| ≤ ε·3^m。wrapped 段階 (指数が負になった後) の黒突入イベントごとに
捕捉走行長 (連続黒ステップ数) を記録し、
  (a) E[捕捉長] が帯・m によらず O(1) か
  (b) 裾 P(捕捉長 ≥ t) が幾何的か
  (c) 白 b=3 ステップの割合が線形か (白点数線形の直接確認)
を測る。補題B の予言: 継続には b_j ≤ ν₂(v) が必要 ⇒ 捕捉長 ≲ ν₂(突入値)/2。
"""
import math
import random

LOG2_3 = math.log2(3)
EPS = 0.01
BMAX = 40


def pascal_sample(rng):
    # P(b) = (b-1)/2^b, b>=2: b = a1+a2, a~Geom(1/2)
    return rng.geometric() + rng.geometric()


class RNG:
    def __init__(self, seed):
        self.r = random.Random(seed)

    def geometric(self):
        # Geom(1/2) on {1,2,...}
        u = self.r.random()
        return min(int(math.floor(-math.log(u, 2))) + 1, BMAX // 2)


def run_band(m, k, walks=1500, seed=1):
    M3 = 3 ** m
    inv2 = pow(2, -1, M3)
    thr = int(EPS * M3)
    rng = RNG(seed)
    runs = []          # 捕捉走行長
    wrapped_steps = 0
    black_steps = 0
    white_b3 = 0
    b3_total = 0
    for w in range(walks):
        L = 0
        v = pow(3, 0, M3)  # 行 j=1 の値は 3^{0}·2^{k-L+1}; 逐次更新で追う
        # 初期値: j=1, L=b1
        b = rng.geometric() + rng.geometric()
        L = b
        e = k - L + 1
        val = (pow(3, 0, M3) * (pow(2, e, M3) if e >= 0 else pow(inv2, -e, M3))) % M3
        in_black = False
        run = 0
        for j in range(2, m // 2 + 1):
            b = rng.geometric() + rng.geometric()
            L += b
            val = (val * 9) % M3
            for _ in range(b):
                val = (val * inv2) % M3
            e = k - L + 1
            if e < 0:  # wrapped 段階のみ計測
                wrapped_steps += 1
                sv = val if val <= M3 // 2 else val - M3
                blk = abs(sv) <= thr
                if b == 3:
                    b3_total += 1
                    if not blk:
                        white_b3 += 1
                if blk:
                    black_steps += 1
                    run += 1
                else:
                    if run > 0:
                        runs.append(run)
                    run = 0
        if run > 0:
            runs.append(run)
    ER = sum(runs) / len(runs) if runs else 0.0
    tail = {}
    for t in (1, 2, 3, 5, 8, 13):
        tail[t] = sum(1 for r in runs if r >= t) / len(runs) if runs else 0.0
    return dict(entries=len(runs), ER=ER, tail=tail,
                black_frac=black_steps / max(wrapped_steps, 1),
                white_b3_frac=white_b3 / max(b3_total, 1),
                wrapped=wrapped_steps)


if __name__ == "__main__":
    print(f"ε = {EPS}; 帯別の捕捉時間統計 (wrapped 段階):")
    for m in (160, 240):
        for tag, k in [("deep k=0.2mα", int(0.2 * m * LOG2_3)),
                       ("mid k=0.5mα", int(0.5 * m * LOG2_3)),
                       ("shoulder δ=0.10", int(m * LOG2_3 - 0.10 * m)),
                       ("shoulder δ=0.05", int(m * LOG2_3 - 0.05 * m))]:
            r = run_band(m, k, walks=1200, seed=m + k)
            t = r["tail"]
            print(f"  m={m} {tag:17s}: E[run]={r['ER']:.2f}  "
                  f"P(≥2)={t[2]:.3f} P(≥5)={t[5]:.3f} P(≥13)={t[13]:.4f}  "
                  f"黒率={r['black_frac']:.4f}  白b3率={r['white_b3_frac']:.3f}  "
                  f"(突入 {r['entries']}, wrapped {r['wrapped']})")
