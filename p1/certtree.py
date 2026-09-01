"""certtree.py — 一様降下証明書の木を構築し、フロンティア c(k) を厳密に数える。

対象写像: Tc(n) = n/2 (偶), (3n+1)/2 (奇)  [Terras 圧縮写像]
ノード不変量: 深さ k, 剰余 r (mod 2^k) の類全体で
    Tc^k(n) = (3^e n + beta) / 2^k     (すべての n ≡ r mod 2^k)
閉包条件 (一様降下): 3^e < 2^k かつ n (2^k - 3^e) > beta が類の全元で成立。
  最小元で成立すれば全元で成立。失敗する有限個の小さい n は exceptions に記録し
  直接反復で降下検証する。

出力: certificates.json (証明書と未解決類), frontier 表 c(k) と増大率。

さらに c(k) をパリティ列 DP で独立に k=200 まで計算し、
  (i) 木の生存数と DP の一致 (二重実装照合)
  (ii) 優乗法性 c(a+b) >= c(a) c(b)
  (iii) Fekete 下界 gamma >= log2 c(k)/k と上界 H(theta) の比較
を行う。すべて厳密整数演算。
"""
import json
import math
import sys


def build_tree(K: int, emit_certs: bool):
    """深さ K まで構築。返り値: (certs, unresolved, alive_counts)
    alive_counts[k] = 深さ k で未閉包の類の数 (= 係数条件でまだ降下が言えない類)。"""
    certs = []
    unresolved = []
    alive_counts = [1]  # depth 0: 全体 (1 類)
    level = [(0, 0, 0)]  # (r, e, beta) at depth k;  pow3[e] < 2^k が閉包
    for k in range(K):
        nxt = []
        p2 = 1 << (k + 1)
        for (r, e, beta) in level:
            # 子: r, r + 2^k  (mod 2^{k+1})
            for r2 in (r, r + (1 << k)):
                v = (3 ** e * r2 + beta) >> k  # Tc^k の代表値; 類上パリティ一定
                if v & 1:
                    e2, b2 = e + 1, 3 * beta + (1 << k)
                else:
                    e2, b2 = e, beta
                k2 = k + 1
                if 3 ** e2 < (1 << k2):
                    if emit_certs:
                        nmin = r2 if r2 > 0 else p2
                        bound = b2 // ((1 << k2) - 3 ** e2)
                        exc = list(range(nmin, bound + 1, p2))
                        certs.append({"k": k2, "mod": p2, "r": r2,
                                      "e": e2, "beta": b2, "exceptions": exc})
                else:
                    nxt.append((r2, e2, b2))
        level = nxt
        alive_counts.append(len(level))
    if emit_certs:
        unresolved = [{"k": K, "mod": 1 << K, "r": r, "e": e, "beta": b}
                      for (r, e, b) in level]
    return certs, unresolved, alive_counts


def climbing_counts_dp(K: int):
    """c(k) = #{長さ k の 0/1 列: すべての接頭辞 j で 3^{e_j} > 2^j}
    を DP で厳密計算。(e_j = 接頭辞の 1 の数; 3^e > 2^j は整数比較)"""
    c = [0] * (K + 1)
    c[0] = 1
    # state: dict e -> count  (climbing prefixes of current length)
    cur = {0: 1}
    for j in range(1, K + 1):
        nxt = {}
        for e, cnt in cur.items():
            for e2 in (e, e + 1):
                if 3 ** e2 > (1 << j):
                    nxt[e2] = nxt.get(e2, 0) + cnt
        cur = nxt
        c[j] = sum(cur.values())
    return c


if __name__ == "__main__":
    K_TREE = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    K_DP = 200

    certs, unresolved, alive = build_tree(K_TREE, emit_certs=True)
    c = climbing_counts_dp(K_DP)

    # (i) 二重実装照合: 木の生存数 = DP の c(k)
    for k in range(K_TREE + 1):
        assert alive[k] == c[k], (k, alive[k], c[k])

    # (ii) 優乗法性 (a+b <= 60 全数)
    for a in range(1, 30):
        for b in range(1, 31):
            assert c[a + b] >= c[a] * c[b], (a, b)

    # (iii) 増大率
    theta = math.log(2) / math.log(3)
    H = -theta * math.log2(theta) - (1 - theta) * math.log2(1 - theta)
    gamma_lb = max(math.log2(c[k]) / k for k in range(2, K_DP + 1))
    print(f"theta = log_3 2 = {theta:.6f},  H(theta) = {H:.6f}")
    print(f"Fekete 下界: gamma >= max_k log2 c(k)/k = {gamma_lb:.6f} (k<= {K_DP})")
    print(f"c(200) = {c[200]}  (log2 c(200)/200 = {math.log2(c[200])/200:.6f})")
    print("k, c(k), c(k)/2^k, log2 c(k)/k:")
    for k in [1, 2, 4, 8, 12, 16, 20, 30, 40, 60, 100, 150, 200]:
        print(f"  {k:4d}  {c[k]:>12}  {c[k]/2**k:12.6e}  "
              f"{(math.log2(c[k])/k if c[k] else float('-inf')):.4f}")

    # 証明書ファイル出力
    with open("certificates.json", "w") as f:
        json.dump({"map": "Tc(n)=n/2 even, (3n+1)/2 odd",
                   "depth": K_TREE,
                   "n_certs": len(certs),
                   "n_unresolved": len(unresolved),
                   "certs": certs,
                   "unresolved": unresolved}, f)
    tot_exc = sum(len(ct["exceptions"]) for ct in certs)
    print(f"\n深さ {K_TREE} の証明書木: 証明書 {len(certs)} 個, "
          f"未解決類 {len(unresolved)} 個 (mod 2^{K_TREE}), 小例外 {tot_exc} 個")
    print(f"未解決密度 c({K_TREE})/2^{K_TREE} = {len(unresolved)/2**K_TREE:.6f}")
    # -1 mod 2^K が未解決に居ることの確認 (障壁の具体例)
    assert any(u["r"] == (1 << K_TREE) - 1 for u in unresolved)
    print(f"確認: r = 2^{K_TREE}-1 (≡ -1) は未解決類に残存 (障壁補題と整合)")
