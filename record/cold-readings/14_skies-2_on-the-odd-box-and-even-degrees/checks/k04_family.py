# k04_family.py -- Grepy Skies 2. Gates for PROOF_ODD_BOX.md, from the definitions:
#  (G1) Theorem 6.1: dim V_Lambda >= |Z_Lambda| for EVERY interlaced pair (V from Definition 4.1).
#  (G2) Lemma 2.3/2.4: options in Lambda form an initial segment; layers are interlaced; (Z)_{>i} = Z_{Lambda_i}
#       (fibres counted by brute force on the points, not by the formula).
#  (G3) Proposition 6.1: V_{Lambda_i} is contained in the honest slice W_{r-1-i}(V_Lambda);
#       control: the same with the slice r-2-i (must fail somewhere: "no slack").
#  (G4) control: pairs of down-sets that are NOT interlaced: dim V vs |Z|.
#  (G5) root: V_root = (D_J) as ideals.
# usage: python3 k04_family.py r m p1,p2,... [noslices]
import sys, time, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from eng2 import *

r = int(sys.argv[1]); m = int(sys.argv[2]); primes = [int(x) for x in sys.argv[3].split(',')]
do_slices = not (len(sys.argv) > 4 and sys.argv[4] == 'noslices')
h = (r - 1) // 2
t0 = time.time()
print("CELL r=%d m=%d h=%d primes=%s" % (r, m, h, primes))
sh = Sh(m, h)
print(" shapes of level m:", " ".join(shname(s) for s in sh))

# points and brute-force fibres
pts_shape = {}
for M in points(m, h):
    pts_shape[M] = shape_of_point(M, h)
shape_count = {}
for M, s in pts_shape.items():
    shape_count[s] = shape_count.get(s, 0) + 1
assert set(shape_count) <= set(sh), "a point has a shape outside Sh_m"
missing = [s for s in sh if s not in shape_count]
print(" shapes with no point:", " ".join(shname(s) for s in missing) or "none")

pairs = interlaced_pairs(m, h)
down_not_inter = [L for L in all_subsets(sh) if is_pair_of_downsets(L, m, h) and not is_interlaced(L, m, h)]
print(" interlaced pairs: %d (incl. empty); pairs of down-sets not interlaced: %d" % (len(pairs), len(down_not_inter)))

# ---------- (G2) combinatorics, independent of the field
bad_chain = bad_layer = bad_fibre = 0
if m >= 1:
    tails = list(points(m - 1, h))
    tail_shape = {M: shape_of_point(M, h) for M in tails}
    for L in pairs:
        # brute-force fibres
        fib = {}
        for Mp in tails:
            c = 0
            for y in range(-h, h + 1):
                if pts_shape[(y,) + Mp] in L: c += 1
            fib[Mp] = c
        for Mp in tails:
            s = tail_shape[Mp]
            if fib[Mp] != FL(L, s[0], s[1], h): bad_fibre += 1
            opts = options(s[0], s[1], h)
            flags = [o in L for o in opts]
            k = sum(flags)
            if flags != [True] * k + [False] * (len(flags) - k): bad_chain += 1
        for i in range(r):
            Li = layer(L, m, h, i)
            if not is_interlaced(Li, m - 1, h): bad_layer += 1
            zi = sum(1 for Mp in tails if fib[Mp] > i)
            zl = sum(1 for Mp in tails if tail_shape[Mp] in Li)
            if zi != zl: bad_fibre += 1
    print(" (G2) Lemma 2.3/2.4 on %d interlaced pairs: chain failures %d, layers not interlaced %d, fibre mismatches %d"
          % (len(pairs), bad_chain, bad_layer, bad_fibre))
    # control: the same tests on the non-interlaced pairs of down-sets
    c_chain = c_layer = 0
    for L in down_not_inter:
        okc = True
        for s in Sh(m - 1, h):
            flags = [o in L for o in options(s[0], s[1], h)]
            k = sum(flags)
            if flags != [True] * k + [False] * (len(flags) - k): okc = False
        if not okc: c_chain += 1
        if any(not is_interlaced(layer(L, m, h, i), m - 1, h) for i in range(r)): c_layer += 1
    print(" (G2-control) non-interlaced pairs of down-sets: %d of %d break the chain, %d of %d have a non-interlaced layer"
          % (c_chain, len(down_not_inter), c_layer, len(down_not_inter)))

# ---------- generators
n = m
I = list(range(n))
tg = time.time()
ngen = {s: len(pattern_products_cached(s, I, n, r)) for s in sh}
print(" pattern products per shape (up to sign):", " ".join("%s:%d" % (shname(s), ngen[s]) for s in sh),
      " [%.1fs]" % (time.time() - tg))
nonhom = sum(1 for s in sh for f in pattern_products_cached(s, I, n, r) if not is_homog(f))
print(" non-homogeneous products:", nonhom)

for p in primes:
    tp = time.time()
    lt = eq = gt = 0
    worst = []
    cache_small = {}
    slice_fail = slice_dim_mismatch = 0
    shifted_fail = shifted_tests = 0
    ncont = 0
    for L in pairs:
        z = sum(shape_count.get(s, 0) for s in L)
        IL = ideal(V_gens(L, I, n, r), n, r, p)
        d = idim(IL)
        if d < z: lt += 1; worst.append((Lname(L), d, z))
        elif d == z: eq += 1
        else: gt += 1; worst.append((Lname(L), d, z))
        if do_slices and m >= 1 and L:
            W = slices(IL, n, r)
            for i in range(r):
                Li = layer(L, m, h, i)
                if Li not in cache_small:
                    cache_small[Li] = ideal(V_gens(Li, list(range(n - 1)), n - 1, r), n - 1, r, p)
                Vs = cache_small[Li]
                zi = sum(1 for Mp in tails if tail_shape[Mp] in Li)
                ncont += 1
                if not contained(Vs, W[r - 1 - i], n - 1, r, p): slice_fail += 1
                if wdim(W[r - 1 - i]) != zi: slice_dim_mismatch += 1
                if i + 1 <= r - 1 and Li:
                    shifted_tests += 1
                    if not contained(Vs, W[r - 2 - i], n - 1, r, p): shifted_fail += 1
    print(" p=%d (G1) Theorem 6.1 on %d interlaced pairs: dim<|Z|: %d   dim=|Z|: %d   dim>|Z|: %d   [%.1fs]"
          % (p, len(pairs), lt, eq, gt, time.time() - tp))
    for w in worst[:12]: print("     NOT EQUAL: %s dim=%d |Z|=%d" % w)
    if do_slices and m >= 1:
        print(" p=%d (G3) Prop 6.1: containments tested %d, FAILURES %d; slices with dim W != |Z_{Lambda_i}|: %d"
              % (p, ncont, slice_fail, slice_dim_mismatch))
        print(" p=%d (G3-control) shifted slice r-2-i: %d of %d containments fail" % (p, shifted_fail, shifted_tests))
    # (G4) control
    ne = 0; ex = None; ltc = 0
    for L in down_not_inter:
        z = sum(shape_count.get(s, 0) for s in L)
        d = idim(ideal(V_gens(L, I, n, r), n, r, p))
        if d != z:
            ne += 1
            if d < z: ltc += 1
            if ex is None: ex = (Lname(L), d, z)
    print(" p=%d (G4-control) non-interlaced pairs of down-sets with dim != |Z|: %d of %d (of which dim<|Z|: %d)%s"
          % (p, ne, len(down_not_inter), ltc, ("  e.g. %s dim=%d |Z|=%d" % ex) if ex else ""))
    # (G5) root
    if m % 2 == 1:
        k = (m - 1) // 2
        root = frozenset([((1,), 0), ((), 1)])
        Iroot = ideal(V_gens(root, I, n, r), n, r, p)
        DJ = []
        for P, rest in pair_sets(I, k):
            f = one(n)
            for (a, b) in P: f = pmul(f, Dpoly(n, a, b, r), r)
            DJ.append(f)
        IDJ = ideal(DJ, n, r, p)
        same = all(len(Iroot[d][0]) == len(IDJ[d][0]) for d in Iroot) and \
               all(member(g, IDJ, n, r, p) for g in V_gens(root, I, n, r))
        print(" p=%d (G5) root k=%d: dim (D_J) = %d, dim V_root = %d, N_r(2k+2) = %d, V_root=(D_J): %s, Hilbert %s"
              % (p, k, idim(IDJ), idim(Iroot), Nr(r, 2 * k + 2), same, hilb(IDJ)))
        if k >= 1 and len(DJ) <= 15:
            drops = []
            for omit in range(len(DJ)):
                drops.append(idim(ideal(DJ[:omit] + DJ[omit + 1:], n, r, p)))
            print(" p=%d (G5-control) one matching removed: dims %s" % (p, sorted(set(drops))))
print("TIME %.1fs" % (time.time() - t0))
