#!/usr/bin/env python3
"""exp31: is E[nu_2 | entry] = O(log m) derivable from Lemma A (pair spacing) alone?

Lemma A (proved, pair-spacing form): chains of depth >= h in the same row are
>= log2(2^h/eps - 1) >= h + log2(1/eps) - 1 positions apart (from 2^Delta w1 = w2 mod 3^d,
w1,w2 odd, |w_i| <= eps 3^d / 2^h).  It constrains the POPULATION of chains but
not their equidistribution.  The walk descends with Pascal steps (mean 3), so a chain
of length D+1 is entered with probability ~ min(1, (D+3)/3) and the entry valuation is
~ D - O(1) (entries land near the top of the chain).  Hence
    E[nu_2 | entry]  ~  sum_w D_w * min(1,(D_w+3)/3) / sum_w min(1,(D_w+3)/3)   (size-biased).

Model instance (saturated population allowed by Lemma A): in a window of length L put,
for every dyadic depth scale h = 2^i, chains of depth h at spacing h + log2(1/eps) - 1.
Finding: the size-biased mean grows like O(log m) (about 2.2 per doubling of m) -- so in the SATURATED case the
per-entry average is O(log m).  But (i) without a lower bound on the number of entries
the per-entry average is not controlled (one deep chain alone gives Theta(m)), and
(ii) what the white-point count needs is the TOTAL of nu_2 over entries, for which
Lemma A gives the deterministic bound sum <= L(ln h_max + O(1)); the implied
black-step bound (L/2)(ln(1.58 d) + C) exceeds L already for small d, i.e. Tao's log
divergence survives.  Hence Lemma A alone yields no unconditional log-log improvement.
"""
import math

ALPHA = math.log2(3)


def size_biased_mean(m, eps=0.02, L=None):
    L = L or 4 * m
    c = math.log2(1 / eps) - 1
    hmax = int(1.58 * m)
    num = den = 0.0
    h = 2
    while h <= hmax:
        spacing = max(h + c, h + 1)                  # Lemma A (pair spacing); chains cannot overlap
        n_chains = L / spacing                       # allowed population at this scale
        p_enter = min(1.0, (h + 3) / 3.0)
        num += n_chains * p_enter * (h - 1)          # entry lands ~1 below the top
        den += n_chains * p_enter
        h *= 2
    return num / den


if __name__ == "__main__":
    print("Lemma-A-allowed chain population: size-biased E[nu2 | entry] vs m")
    prev = None
    for m in (64, 128, 256, 512, 1024, 2048):
        v = size_biased_mean(m)
        ratio = f"  ratio to log2(m): {v / math.log2(m):.2f}   ratio to m: {v / m:.4f}"
        print(f"  m={m:5d}: E ~ {v:8.2f}{ratio}")
    print("=> saturated model: O(log m) per entry (~2.2 per doubling of m).  Total-form bound is deterministic but"
          " its black-step consequence is vacuous already for small d (log divergence survives).")
