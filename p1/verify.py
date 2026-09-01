"""verify.py — certificates.json の独立検証器。探索器 (certtree.py) より単純。

検査項目:
  V1 被覆: 証明書 + 未解決類が mod 2^K の全剰余を重複なく被覆する (ビット表)。
  V2 各証明書のアフィン表示: 記号反復 (n = 2^K q + r の一次式) で Tc を k 回
     適用し、パリティが q に依らず一定であること、最終形が (3^e n + beta)/2^k に
     一致することを再導出する。
  V3 降下: 3^e < 2^k, かつ例外リスト外の類最小元で n (2^k - 3^e) > beta。
     例外の各 n は直接反復で n 未満へ降下することを確認。
  V4 未解決類: 係数条件 3^e >= 2^k を確認 (まだ降下が言えないことの検算)。
"""
import json
import sys


def tc(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def main(path="certificates.json"):
    data = json.load(open(path))
    K = data["depth"]
    P = 1 << K
    certs, unresolved = data["certs"], data["unresolved"]

    # V1 被覆
    cover = bytearray(P)
    for item in certs + unresolved:
        step = item["mod"]
        assert step <= P and P % step == 0
        for r in range(item["r"], P, step):
            assert cover[r] == 0, f"overlap at {r}"
            cover[r] = 1
    assert all(cover), "coverage gap"

    # V2 + V3
    for ct in certs:
        k, mod, r, e, beta = ct["k"], ct["mod"], ct["r"], ct["e"], ct["beta"]
        assert mod == 1 << k
        # 記号反復: n = mod*q + r を (c1*q + c0) として k 回反復
        c1, c0 = mod, (r if r > 0 else mod)  # 代表 n>=1; c1 の係数は全 q>=0 で有効
        c1b, c0b = mod, r + mod              # 第二代表 (q を 1 ずらす) でパリティ照合
        for _ in range(k):
            p, pb = c0 & 1, c0b & 1
            assert p == pb, "parity not constant on class"
            if p:
                c1, c0 = 3 * c1, 3 * c0 + 1
                c1b, c0b = 3 * c1b, 3 * c0b + 1
            assert c0 % 2 == 0 and c1 % 2 == 0, "not divisible"
            c1, c0 = c1 // 2, c0 // 2
            assert c1b % 2 == 0 and c0b % 2 == 0, "not divisible (2nd rep)"
            c1b, c0b = c1b // 2, c0b // 2
        # アフィン形一致: Tc^k(mod*q + r) = c1*q + c0 == (3^e (mod q + r) + beta)/2^k
        assert c1 * (1 << k) == 3 ** e * mod, "coefficient mismatch"
        rep = r if r > 0 else mod
        assert c0 * (1 << k) == 3 ** e * rep + beta, "constant mismatch"
        # 降下
        assert 3 ** e < (1 << k), "not contracting"
        gap = (1 << k) - 3 ** e
        exc = set(ct["exceptions"])
        nmin = rep
        while nmin in exc:
            nmin += mod
        assert nmin * gap > beta, "descent fails at minimal non-exception"
        for n in exc:
            if n == 1:
                continue  # 自明周期の終点: 予想の主張は「1 に到達」であり降下不要
            m = n
            steps = 0
            while m >= n:
                m = tc(m)
                steps += 1
                assert steps < 10 ** 6
        # 例外も直接降下 OK

    # V4
    for u in unresolved:
        assert 3 ** u["e"] >= (1 << u["k"])

    print(f"verify.py: OK — {len(certs)} certificates verified, "
          f"{len(unresolved)} unresolved classes at mod 2^{K}, exact cover confirmed")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "certificates.json")
