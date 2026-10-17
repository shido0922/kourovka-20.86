"""
Computer checks for the counterexample to Kourovka Notebook Problem 20.86 (see README.md).

Written by Claude (Anthropic) as an independent re-check, without reusing the code of the
first verification.  Everything (finite field, matrices, group closure, rank, brute force) is
implemented here from scratch.  Requires Python 3 and numpy; the brute force (part D) takes a
few minutes.

Claims checked (see README.md):
  A. GF(8) built from scratch (field axioms verified exhaustively).
  B. E = <x, y> <= GL_7(F_8): |E| = 343, exponent 7, Z(E) = scalars (7),
     E' = Z(E), E/Z(E) elementary abelian  ->  extraspecial 7^{1+2}_+.
     E spans M_7(F_8) (absolutely irreducible), C_V(E) = 0.
  C. For each a in E: dim ker(N_a), N_a = I + a + ... + a^6, and dim ker(a - I).
     |G_7| = sum 8^{dim ker N_a};  cross-check with Knapp-Schmid Lemma 3
     f_p = (1/|P|) sum_x s_p / psi(x), psi(x) = |C_V(x)|.
  D. Brute force over ALL 2^21 vectors v and ALL 343 a: (v,a)^7 computed by six
     applications of the group law (v,a)(u,b) = (v + a u, ab) with V encoded as
     21-bit integers (char 2: vector addition = XOR).  No N_a formula is used
     for the count; the formula (v,a)^7 = (N_a v, 1) is then compared against it.
     Sylow count: number of distinct conjugates of E_0 = number of distinct
     pairs ((x-1)v, (y-1)v) over v in V  (each conjugate E_0^{(v,1)} has exactly
     one element with E-component x, namely ((1+x)v, x), and one with y).
  E. Exact integers: k, f, l, l^7 < k^6, ratio, Gheri ratio, identity.
  F. Small analogues (p,Q) = (3,4), (3,7) by GENERIC brute force (element
     orders by repeated multiplication, Sylow subgroups as sets of conjugates),
     and (5,11) by vectorised brute force; compared with the family formulas.
  G. Family table for all primes p <= 260 with exact integers.

Run:  python verify.py  [--skip-brute] [--skip-511]
"""
import sys, time, itertools, math
sys.stdout.reconfigure(encoding="utf-8")
from fractions import Fraction
import numpy as np

T0 = time.time()
OUT = []
def log(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    OUT.append(s)
def section(title):
    log("\n" + "=" * 78 + "\n" + title + "\n" + "=" * 78)
def elapsed():
    return "[%.1f s]" % (time.time() - T0)

# ----------------------------------------------------------------------------
# A. finite fields
# ----------------------------------------------------------------------------
def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
    return True

def prime_power(Q):
    """(r, n) with Q = r^n, r prime; None otherwise."""
    for r in range(2, Q + 1):
        if Q % r == 0:
            if not is_prime(r):
                return None
            n, m = 0, Q
            while m % r == 0:
                m //= r
                n += 1
            return (r, n) if m == 1 else None
    return None

class GF:
    """GF(r^n), n <= 3.  Elements are integers 0..q-1 encoding the coefficient
    vector (base r, little-endian) w.r.t. the basis 1, t, t^2 of F_r[t]/(m(t)),
    m monic irreducible (found by brute force: for n in {2,3} irreducible iff no
    root in F_r).  Tables ADD, MUL, NEG, INV are numpy uint8 arrays."""
    def __init__(self, r, n):
        assert is_prime(r) and 1 <= n <= 3
        self.r, self.n, self.q = r, n, r ** n
        q = self.q
        if n == 1:
            self.poly = [0]
        else:
            found = None
            for coeffs in itertools.product(range(r), repeat=n):
                if coeffs[0] == 0:
                    continue
                if all((pow(t, n, r) + sum(coeffs[i] * pow(t, i, r) for i in range(n))) % r
                       for t in range(r)):
                    found = list(coeffs)
                    break
            assert found is not None
            self.poly = found          # m(t) = t^n + sum poly[i] t^i

        def dec(e):
            v = []
            for _ in range(n):
                v.append(e % r)
                e //= r
            return v

        def enc(v):
            e = 0
            for c in reversed(v):
                e = e * r + (c % r)
            return e

        self.dec, self.enc = dec, enc
        ADD = np.zeros((q, q), dtype=np.uint8)
        MUL = np.zeros((q, q), dtype=np.uint8)
        for a in range(q):
            va = dec(a)
            for b in range(q):
                vb = dec(b)
                ADD[a, b] = enc([(va[i] + vb[i]) % r for i in range(n)])
                prod = [0] * (2 * n - 1)
                for i in range(n):
                    for j in range(n):
                        prod[i + j] = (prod[i + j] + va[i] * vb[j]) % r
                for d in range(2 * n - 2, n - 1, -1):
                    c = prod[d]
                    if c:
                        prod[d] = 0
                        for i in range(n):          # t^d = t^(d-n) * t^n, t^n = -sum poly[i] t^i
                            prod[d - n + i] = (prod[d - n + i] - c * self.poly[i]) % r
                MUL[a, b] = enc(prod[:n])
        self.ADD, self.MUL = ADD, MUL
        self.zero, self.one = 0, enc([1] + [0] * (n - 1))
        NEG = np.zeros(q, dtype=np.uint8)
        INV = np.zeros(q, dtype=np.uint8)
        for a in range(q):
            NEG[a] = [b for b in range(q) if ADD[a, b] == 0][0]
            if a:
                inv = [b for b in range(q) if MUL[a, b] == self.one]
                assert len(inv) == 1, "not a field"
                INV[a] = inv[0]
        self.NEG, self.INV = NEG, INV

    def check_axioms(self):
        q, A, M = self.q, self.ADD.astype(np.int64), self.MUL.astype(np.int64)
        assert (A == A.T).all() and (M == M.T).all()
        assert all(A[a, 0] == a and M[a, self.one] == a and M[a, 0] == 0 for a in range(q))
        for a in range(q):
            assert (A[A[a, :], :] == A[a, A]).all()          # (a+b)+c = a+(b+c)
            assert (M[M[a, :], :] == M[a, M]).all()          # (ab)c = a(bc)
            assert (M[a, A] == A[np.ix_(M[a, :], M[a, :])]).all()   # a(b+c) = ab+ac
        # multiplicative group cyclic of order q-1 (every nonzero element has x^(q-1)=1)
        for a in range(1, q):
            assert self.power(a, q - 1) == self.one
        return True

    def power(self, a, e):
        res = self.one
        for _ in range(e):
            res = int(self.MUL[res, a])
        return res

    def root_of_unity(self, p):
        """an element of multiplicative order exactly p (needs p | q-1)."""
        assert (self.q - 1) % p == 0
        for a in range(1, self.q):
            if self.power(a, p) == self.one and a != self.one:
                # order divides p, p prime, a != 1  -> order p
                return a
        raise AssertionError

# ----------------------------------------------------------------------------
# matrices over GF  (numpy uint8 arrays of element codes)
# ----------------------------------------------------------------------------
def mat_mul(F, A, B):
    n = A.shape[0]
    C = np.zeros((n, n), dtype=np.uint8)
    for j in range(n):
        C = F.ADD[C, F.MUL[A[:, j][:, None], B[j, :][None, :]]]
    return C

def mat_add(F, A, B):
    return F.ADD[A, B]

def mat_neg(F, A):
    return F.NEG[A]

def mat_vec(F, A, v):
    n = A.shape[0]
    w = np.zeros(n, dtype=np.uint8)
    for j in range(n):
        w = F.ADD[w, F.MUL[A[:, j], v[j]]]
    return w

def mat_pow(F, A, e):
    n = A.shape[0]
    R = identity(F, n)
    for _ in range(e):
        R = mat_mul(F, R, A)
    return R

def identity(F, n):
    I = np.zeros((n, n), dtype=np.uint8)
    for i in range(n):
        I[i, i] = F.one
    return I

def scalar(F, n, c):
    S = np.zeros((n, n), dtype=np.uint8)
    for i in range(n):
        S[i, i] = c
    return S

def mat_rank(F, A):
    M = A.copy()
    n, m = M.shape
    row = 0
    for col in range(m):
        piv = None
        for i in range(row, n):
            if M[i, col]:
                piv = i
                break
        if piv is None:
            continue
        if piv != row:
            M[[row, piv]] = M[[piv, row]]
        inv = F.INV[M[row, col]]
        M[row] = F.MUL[inv, M[row]]
        for i in range(n):
            if i != row and M[i, col]:
                c = M[i, col]
                M[i] = F.ADD[M[i], F.NEG[F.MUL[c, M[row]]]]
        row += 1
        if row == n:
            break
    return row

def closure(F, gens):
    """all products of generators (finite -> the generated group)."""
    n = gens[0].shape[0]
    I = identity(F, n)
    elems = {I.tobytes(): I}
    frontier = [I]
    while frontier:
        new = []
        for A in frontier:
            for g in gens:
                B = mat_mul(F, A, g)
                kb = B.tobytes()
                if kb not in elems:
                    elems[kb] = B
                    new.append(B)
        frontier = new
    return list(elems.values())

def build_E(F, p):
    """x = diag(1, w, ..., w^{p-1}), y = cyclic shift e_i -> e_{i+1}; E = <x, y>."""
    w = F.root_of_unity(p)
    x = np.zeros((p, p), dtype=np.uint8)
    y = np.zeros((p, p), dtype=np.uint8)
    for i in range(p):
        x[i, i] = F.power(w, i)
        y[(i + 1) % p, i] = F.one         # y e_i = e_{i+1}  (column i has a 1 in row i+1)
    return w, x, y, closure(F, [x, y])

def structure_checks(F, p, w, x, y, E):
    """|E| = p^3, exponent p, Z(E) = scalars, E' = Z(E), spans M_p, C_V(E) = 0."""
    n = p
    I = identity(F, n)
    log("|E| =", len(E), "(expected %d)" % p ** 3)
    assert len(E) == p ** 3
    # exponent
    orders = {}
    for a in E:
        R = a.copy()
        o = 1
        while not np.array_equal(R, I):
            R = mat_mul(F, R, a)
            o += 1
            assert o <= p ** 3
        orders[o] = orders.get(o, 0) + 1
    log("element orders in E:", dict(sorted(orders.items())))
    assert set(orders) <= {1, p} and orders.get(p, 0) == p ** 3 - 1
    # xy = w yx
    assert np.array_equal(mat_mul(F, x, y), mat_mul(F, scalar(F, n, w), mat_mul(F, y, x)))
    # center
    Z = [a for a in E if np.array_equal(mat_mul(F, a, x), mat_mul(F, x, a))
         and np.array_equal(mat_mul(F, a, y), mat_mul(F, y, a))]
    scal = {scalar(F, n, F.power(w, c)).tobytes() for c in range(p)}
    assert len(scal) == p
    assert len(Z) == p and {a.tobytes() for a in Z} == scal
    log("Z(E) = the", p, "scalar matrices w^c I  : OK")
    # derived subgroup: all commutators a b a^-1 b^-1 are scalars, and they fill Z(E)
    inv = [mat_pow(F, a, p - 1) for a in E]           # a^-1 = a^(p-1) since a^p = 1
    for a, ai in zip(E, inv):
        assert np.array_equal(mat_mul(F, a, ai), I)
    comms = set()
    for a, ainv in zip(E, inv):
        for b, binv in zip(E, inv):
            c = mat_mul(F, mat_mul(F, a, b), mat_mul(F, ainv, binv))
            comms.add(c.tobytes())
    assert comms == scal
    log("set of commutators = Z(E)  (so E' = Z(E), E/Z(E) abelian of order %d, exponent %d): OK"
        % (p ** 2, p))
    # absolute irreducibility: E spans M_n(F)  (rank 49 of the 343 x 49 matrix)
    S = np.array([a.reshape(-1) for a in E], dtype=np.uint8)
    rk = mat_rank(F, S)
    log("dim span_F(E) in M_%d(F_%d) = %d (expected %d)" % (n, F.q, rk, n * n))
    assert rk == n * n
    # C_V(E) = 0 : rank of stacked (a - I) over all a is n
    stack = np.vstack([mat_add(F, a, mat_neg(F, I)) for a in E])
    rk2 = mat_rank(F, stack)
    log("rank of stacked (a - I), a in E:", rk2, "-> C_V(E) = 0 :", rk2 == n)
    assert rk2 == n
    # O_p(G) = 1 follows (any normal p-subgroup N has N ∩ V = 1 and centralises V; E faithful)
    return Z

def kernel_data(F, p, w, E):
    """for each a: dim ker N_a and dim ker (a - I); returns tallies and |G_p|."""
    n = p
    I = identity(F, n)
    Z = {scalar(F, n, F.power(w, c)).tobytes() for c in range(p)}
    tally = {}            # (class, dim ker N_a, dim ker (a-I)) -> count
    Gp = 0
    lemma3_sum = Fraction(0)
    s = F.q ** p
    for a in E:
        N = I.copy()
        R = I.copy()
        for _ in range(p - 1):
            R = mat_mul(F, R, a)
            N = mat_add(F, N, R)
        dkN = n - mat_rank(F, N)
        dkF = n - mat_rank(F, mat_add(F, a, mat_neg(F, I)))
        cls = "identity" if np.array_equal(a, I) else ("central" if a.tobytes() in Z else "noncentral")
        key = (cls, dkN, dkF)
        tally[key] = tally.get(key, 0) + 1
        Gp += F.q ** dkN
        lemma3_sum += Fraction(s, F.q ** dkF)      # s_p / psi(a), psi(a) = |C_V(a)| = q^{dim ker(a-I)}
    log("tally (class, dim ker N_a, dim ker(a-I)) -> count:")
    for key in sorted(tally):
        log("   ", key, "->", tally[key])
    f_lemma3 = lemma3_sum / (p ** 3)
    return tally, Gp, f_lemma3

# ----------------------------------------------------------------------------
# D. brute force for p = 7 with 21-bit encoding (char 2)
# ----------------------------------------------------------------------------
def enc_vec(v):
    return int(sum(int(v[i]) << (3 * i) for i in range(7)))

def dec_vec(e):
    return np.array([(e >> (3 * i)) & 7 for i in range(7)], dtype=np.uint8)

def lin_tables(F, A):
    """three 128-entry tables for the F_2-linear map v -> A v on 21-bit codes."""
    T = []
    for c in range(3):
        tab = np.zeros(128, dtype=np.int64)
        for m in range(128):
            tab[m] = enc_vec(mat_vec(F, A, dec_vec(m << (7 * c))))
        T.append(tab)
    return T

def apply_lin(T, v):
    return T[0][v & 127] ^ T[1][(v >> 7) & 127] ^ T[2][v >> 14]

def brute_force_p7(F, w, x, y, E):
    n = 7
    I = identity(F, n)
    assert F.q == 8 and all(int(F.ADD[a, b]) == (a ^ b) for a in range(8) for b in range(8)), \
        "GF(8) addition must be XOR on the codes"
    allv = np.arange(1 << 21, dtype=np.int64)
    # sanity: tables reproduce mat_vec on random vectors
    rng = np.random.default_rng(20261015)
    for A in (x, y, E[123], E[300]):
        T = lin_tables(F, A)
        for _ in range(50):
            v = rng.integers(0, 8, size=7, dtype=np.uint8)
            assert enc_vec(mat_vec(F, A, v)) == int(apply_lin(T, np.int64(enc_vec(v))))
    # (v,a)^7 for all v, all a, by six applications of the group law
    Z = {scalar(F, n, F.power(w, c)).tobytes() for c in range(7)}
    tally = {}
    total = 0
    formula_ok = True
    for idx, a in enumerate(E):
        T = lin_tables(F, a)
        wv = allv.copy()                      # (v, a)^1 = (v, a)
        for _ in range(6):
            wv = allv ^ apply_lin(T, wv)      # (v,a)(w, a^m) = (v + a w, a^{m+1})
        # now (v,a)^7 = (wv, a^7) and a^7 = I (checked in structure_checks)
        n7 = int(np.count_nonzero(wv == 0))
        # (v,a)^14 = (wv, I)(wv, I) = (wv + wv, I) = (0, I): every element has order | 14,
        # so p-element <=> (v,a)^7 = 1.  Check explicitly:
        assert np.all((wv ^ wv) == 0)
        # compare with the formula (v,a)^7 = (N_a v, I)
        N = I.copy(); R = I.copy()
        for _ in range(6):
            R = mat_mul(F, R, a); N = mat_add(F, N, R)
        TN = lin_tables(F, N)
        if not np.array_equal(apply_lin(TN, allv), wv):
            formula_ok = False
        cls = "identity" if np.array_equal(a, I) else ("central" if a.tobytes() in Z else "noncentral")
        tally[(cls, n7)] = tally.get((cls, n7), 0) + 1
        total += n7
        if idx % 49 == 48:
            log("   ... %d / 343 elements done %s" % (idx + 1, elapsed()))
    log("brute force: (class, #v with (v,a)^7 = 1) -> #a :")
    for key in sorted(tally):
        log("   ", key, "->", tally[key])
    log("brute force |G_7| =", total)
    log("formula (v,a)^7 = (N_a v, 1) agrees with the group law for all 7.2e8 elements:", formula_ok)
    assert formula_ok
    # Sylow count: distinct pairs ((1+x)v, (1+y)v)
    Tx, Ty = lin_tables(F, x), lin_tables(F, y)
    u1 = allv ^ apply_lin(Tx, allv)
    u2 = allv ^ apply_lin(Ty, allv)
    pairs = (u1 << 21) | u2
    ndist = len(np.unique(pairs))
    log("distinct conjugates E_0^{(v,1)} (via the pair of elements with E-part x, y):", ndist,
        "= 2^21 :", ndist == 1 << 21)
    # centraliser C_V(E) = C_V(x) ∩ C_V(y)
    fixed = np.count_nonzero((apply_lin(Tx, allv) == allv) & (apply_lin(Ty, allv) == allv))
    log("#v with xv = v and yv = v :", int(fixed), "(expected 1)")
    assert ndist == 1 << 21 and fixed == 1
    return total

# ----------------------------------------------------------------------------
# F. small analogues, generic brute force
# ----------------------------------------------------------------------------
def family_formulas(p, Q):
    s = Q ** p
    k = (s - 1) // p
    assert k * p == s - 1
    Gp = 1 + (p - 1) * Q ** p + (p ** 3 - p) * Q ** (p - 1)
    assert Gp % p ** 3 == 0
    f = Gp // p ** 3
    assert (f - 1) % (p - 1) == 0
    l = (f - 1) // (p - 1)
    l2 = (Q ** p + p * (p + 1) * Q ** (p - 1) - (p * p + p + 1))
    assert l2 % p ** 3 == 0 and l2 // p ** 3 == l
    return s, k, Gp, f, l

def generic_small(p, Q):
    """fully generic brute force: orders by repeated multiplication, Sylow subgroups as
    sets of conjugates of E_0.  Feasible for |G| up to ~10^4."""
    r, n = prime_power(Q)
    F = GF(r, n); F.check_axioms()
    w, x, y, E = build_E(F, p)
    assert len(E) == p ** 3
    Eidx = {a.tobytes(): i for i, a in enumerate(E)}
    I = identity(F, p)
    # multiplication table of E (indices) and action tables a*v
    mulE = np.zeros((len(E), len(E)), dtype=np.int64)
    for i, a in enumerate(E):
        for j, b in enumerate(E):
            mulE[i, j] = Eidx[mat_mul(F, a, b).tobytes()]
    V = list(itertools.product(range(Q), repeat=p))
    Vidx = {v: i for i, v in enumerate(V)}
    Varr = np.array(V, dtype=np.uint8)
    act = np.zeros((len(E), len(V)), dtype=np.int64)
    for i, a in enumerate(E):
        # a applied to all vectors at once
        W = np.zeros_like(Varr)
        for j in range(p):
            W = F.ADD[W, F.MUL[a[:, j][None, :], Varr[:, j][:, None]]]
        act[i] = [Vidx[tuple(int(c) for c in row)] for row in W]
    # precompute vector addition table (|V|^2 may be big: 343^2 = 117649 fine)
    addT = np.zeros((len(V), len(V)), dtype=np.int64)
    for i in range(len(V)):
        rows = F.ADD[Varr[i][None, :], Varr]
        addT[i] = [Vidx[tuple(int(c) for c in rw)] for rw in rows]
    e_id = Eidx[I.tobytes()]
    zero = Vidx[tuple([0] * p)]
    def gmul(g, h):      # g = (vi, ai)
        vi, ai = g; ui, bi = h
        return (int(addT[vi, act[ai, ui]]), int(mulE[ai, bi]))
    ident = (zero, e_id)
    # orders of all elements
    order_count = {}
    pelems = 0
    for vi in range(len(V)):
        for ai in range(len(E)):
            g = (vi, ai)
            h = g; o = 1
            while h != ident:
                h = gmul(g, h); o += 1
            order_count[o] = order_count.get(o, 0) + 1
            oo = o
            while oo % p == 0:
                oo //= p
            if oo == 1:
                pelems += 1
    log("  (p,Q)=(%d,%d): |G| = %d, element orders: %s" % (p, Q, len(V) * len(E), dict(sorted(order_count.items()))))
    # Sylow p-subgroups: conjugates of E_0 = {(0, a)}
    E0 = frozenset((zero, ai) for ai in range(len(E)))
    def ginv(g):
        vi, ai = g
        # (v,a)^-1 = (-a^-1 v, a^-1): find by brute force a^-1 index
        ainv = int(np.where(mulE[ai] == e_id)[0][0])
        nv = Vidx[tuple(int(c) for c in F.NEG[Varr[act[ainv, vi]]])]
        return (nv, ainv)
    conj = set()
    for vi in range(len(V)):
        g = (vi, e_id)              # conjugating by (v, 1) suffices: (v,a) = (v,1)(0,a) and (0,a) normalises E_0
        gi = ginv(g)
        conj.add(frozenset(gmul(gmul(g, h), gi) for h in E0))
    # also conjugate by a sample of general elements to make sure no new conjugates appear
    rng = np.random.default_rng(7)
    for _ in range(200):
        g = (int(rng.integers(len(V))), int(rng.integers(len(E))))
        gi = ginv(g)
        conj.add(frozenset(gmul(gmul(g, h), gi) for h in E0))
    sp = len(conj)
    # every conjugate is a subgroup of order p^3 whose elements are p-elements: check union = p-elements
    union = set().union(*conj)
    log("  s_p (distinct conjugates of E_0) = %d, |G_p| (orders a power of p) = %d, |union of Sylows| = %d"
        % (sp, pelems, len(union)))
    assert len(union) == pelems
    s, k, Gp, f, l = family_formulas(p, Q)
    log("  family formulas: s_p = %d, |G_p| = %d  -> match: %s" % (s, Gp, (sp, pelems) == (s, Gp)))
    assert (sp, pelems) == (s, Gp)
    return sp, pelems

def vectorised_small(p, Q):
    """(v,a)^p for all v by p-1 applications of the group law (odd characteristic, table based)."""
    r, n = prime_power(Q)
    F = GF(r, n); F.check_axioms()
    w, x, y, E = build_E(F, p)
    assert len(E) == p ** 3
    I = identity(F, p)
    V = np.array(list(itertools.product(range(Q), repeat=p)), dtype=np.uint8)   # Q^p x p
    def act(a, W):
        R = np.zeros_like(W)
        for j in range(p):
            R = F.ADD[R, F.MUL[a[:, j][None, :], W[:, j][:, None]]]
        return R
    total = 0
    for a in E:
        assert np.array_equal(mat_pow(F, a, p), I)
        W = V.copy()
        for _ in range(p - 1):
            W = F.ADD[V, act(a, W)]
        # (v,a)^p = (W, 1);  (W,1)^r = (r W, 1) = (0,1) since char r, so orders | p r and
        # p-element <=> W = 0
        total += int(np.count_nonzero(~W.any(axis=1)))
    # Sylow count: distinct pairs ((x-1)v, (y-1)v)
    U1 = F.ADD[act(x, V), F.NEG[V]]
    U2 = F.ADD[act(y, V), F.NEG[V]]
    keys = np.concatenate([U1, U2], axis=1)
    ndist = len(np.unique(keys, axis=0))
    s, k, Gp, f, l = family_formulas(p, Q)
    log("  (p,Q)=(%d,%d): brute |G_p| = %d (formula %d), s_p = %d (formula %d)" % (p, Q, total, Gp, ndist, s))
    assert total == Gp and ndist == s
    return ndist, total

# ----------------------------------------------------------------------------
def main():
    skip_brute = "--skip-brute" in sys.argv
    skip_511 = "--skip-511" in sys.argv

    section("A. GF(8) from scratch")
    F8 = GF(2, 3)
    log("modulus: t^3 + %s  (coefficients of 1, t, t^2: %s)" %
        (" + ".join("%d t^%d" % (c, i) for i, c in enumerate(F8.poly) if c), F8.poly))
    F8.check_axioms()
    log("field axioms (exhaustive), x^7 = 1 for all x != 0: OK")
    w = F8.root_of_unity(7)
    log("omega =", w, "(code), powers:", [F8.power(w, i) for i in range(8)])
    assert len({F8.power(w, i) for i in range(7)}) == 7

    section("B. E = <x, y> <= GL_7(F_8)")
    w, x, y, E = build_E(F8, 7)
    Z = structure_checks(F8, 7, w, x, y, E)
    log(elapsed())

    section("C. kernels of N_a and of (a - 1), |G_7| by the fibre formula, Lemma 3 cross-check")
    tally, Gp, f_lemma3 = kernel_data(F8, 7, w, E)
    log("|G_7| = sum_a 8^(dim ker N_a) =", Gp)
    assert Gp == 1 + 6 * 8 ** 7 + 336 * 8 ** 6 == 100663297
    log("Knapp-Schmid Lemma 3: f_7 = (1/343) sum_a s_7/psi(a) =", f_lemma3, "  (= |G_7|/343 :", f_lemma3 == Fraction(Gp, 343), ")")
    assert f_lemma3 == Fraction(Gp, 343)
    # geometric-mean version (Knapp-Schmid Lemma 6: = s^{(p-1)/p} for exponent p)
    logprod = sum(cnt * dkF * math.log(8) for (cls, dkN, dkF), cnt in tally.items())   # sum log psi(a)
    fhat = 2 ** 21 / math.exp(logprod / 343)
    log("f-hat = s / (prod psi)^(1/343) = %.6f  (s^(6/7) = %d)" % (fhat, 2 ** 18))
    log(elapsed())

    section("D. brute force over all 343 * 2^21 elements (group law only)")
    if skip_brute:
        log("skipped (--skip-brute)")
    else:
        tot = brute_force_p7(F8, w, x, y, E)
        assert tot == Gp
        log(elapsed())

    section("E. exact integers")
    s = 2 ** 21
    k = (s - 1) // 7
    assert 7 * k == s - 1
    f = Gp // 343
    assert 343 * f == Gp
    l = (f - 1) // 6
    assert 6 * l == f - 1
    log("s_7 = %d = 1 + 7*%d,  k = %d" % (s, k, k))
    log("|G_7| = %d = 343 * %d,  f_7 = %d = 1 + 6*%d,  l = %d" % (Gp, f, f, l, l))
    assert k == 299593 and f == 293479 and l == 48913
    assert 343 * l == 2 ** 24 - 57
    log("l^7 =", l ** 7)
    log("k^6 =", k ** 6)
    log("l^7 < k^6 :", l ** 7 < k ** 6, "  ratio = %.8f" % (l ** 7 / k ** 6))
    assert l ** 7 < k ** 6
    gheri = Fraction(f ** 7, s ** 6)
    log("Gheri ratio f^7 / s^6 = %.6f  (>= 1 : %s)" % (float(gheri), gheri >= 1))
    ident = gheri * Fraction(f - 1, f) ** 7 / Fraction(s - 1, s) ** 6 * Fraction(7 ** 6, 6 ** 7)
    log("identity  l^7/k^6 = (f^7/s^6)(1-1/f)^7(1-1/s)^-6 7^6/6^7 :", ident == Fraction(l ** 7, k ** 6))
    assert ident == Fraction(l ** 7, k ** 6)
    # hand estimate from README (3.7): 2^42 < 0.93 * 7^15 and (1-2^-21)^-6 < 1.01
    log("2^42 = %d < 0.93*7^15 = %.0f : %s" % (2 ** 42, 0.93 * 7 ** 15, 2 ** 42 < 0.93 * 7 ** 15))
    log("PSL_3(7): |G| = %d, s_7 = %d, k = %d, |G_7| = 7^6 (Steinberg), f = 343, l = %d, l^7 >= k^6: %s"
        % (343 * 48 * 342 // 3, 343 * 48 * 342 // 3 // (343 * 12), (456 - 1) // 7, (343 - 1) // 6, 57 ** 7 >= 65 ** 6))

    section("F. small analogues of the family")
    for (p, Q) in [(3, 4), (3, 7)]:
        generic_small(p, Q)
        log("  " + elapsed())
    if skip_511:
        log("  (5,11) skipped (--skip-511)")
    else:
        vectorised_small(5, 11)
        log("  " + elapsed())

    section("G. family table, exact integers, all primes p <= 260")
    breaking = {}
    for p in range(3, 261):
        if not is_prime(p):
            continue
        bad = []
        for m in range(1, 40):
            Q = m * p + 1
            if prime_power(Q) is None:
                continue
            s, k, Gp, f, l = family_formulas(p, Q)
            LP, KP = l ** p, k ** (p - 1)                      # exact integers
            ratio_log = p * math.log(l) - (p - 1) * math.log(k)
            gheri_log = p * math.log(f) - (p - 1) * math.log(s)
            if LP < KP:
                bad.append((Q, m, math.exp(ratio_log), math.exp(gheri_log)))
            # lower bound (Q+p^2+p-1)^p / p^(2p+1) <= ratio < upper bound (exact integer comparisons)
            assert (Q + p * p + p - 1) ** p * KP <= p ** (2 * p + 1) * LP, (p, Q)
            assert LP * p ** (2 * p + 1) * (Q ** p - 1) ** (p - 1) < (Q + p * p + p) ** p * KP * Q ** (p * (p - 1)), (p, Q)
            lb_gt_1 = (Q + p * p + p - 1) ** p > p ** (2 * p + 1)
            # the lower bound increases with Q, so once it exceeds 1 no larger Q can break
            if lb_gt_1 and m >= 3:
                break
        if bad:
            breaking[p] = bad
    log("primes p <= 260 for which some Q = mp+1 (prime power) gives l^p < k^(p-1):")
    for p in sorted(breaking):
        log("   p = %3d : " % p + ", ".join("Q=%d (m=%d) ratio=%.6f gheri=%.3f" % b for b in breaking[p]))
    expected_list = [7, 23, 29, 31, 41, 53, 83, 89, 113, 127, 131, 139, 163, 173, 179, 191, 193, 199, 233, 239, 251]
    log("matches the list in README:", sorted(breaking) == expected_list)
    assert sorted(breaking) == expected_list
    # p = 3, 5 never break: lower bound at the smallest Q already > 1
    for p, Qmin in [(3, 4), (5, 11)]:
        lb = Fraction((Qmin + p * p + p - 1) ** p, p ** (2 * p + 1))
        log("p = %d: lower bound at Q = %d is %.4f > 1 -> never breaks" % (p, Qmin, float(lb)))
        assert lb > 1
    # Mersenne primes p >= 7 with Q = p + 1 ; Sophie Germain-type Q = 2p+1 for p >= 23
    for p in [7, 31, 127]:
        s, k, Gp, f, l = family_formulas(p, p + 1)
        log("Mersenne p = %d, Q = %d: l^p < k^(p-1) : %s" % (p, p + 1, l ** p < k ** (p - 1)))
        assert l ** p < k ** (p - 1)
    s, k, Gp, f, l = family_formulas(8191, 8192)       # too big for exact powers; use logs
    lr = 8191 * math.log(l) - 8190 * math.log(k)
    log("Mersenne p = 8191, Q = 8192: log(l^p / k^(p-1)) = %.3f (< 0 : %s)" % (lr, lr < 0))
    assert lr < 0
    for p in [23, 29, 41, 53, 83, 89, 113, 131, 173, 179, 191, 233, 239, 251, 281, 293]:
        if prime_power(2 * p + 1):
            s, k, Gp, f, l = family_formulas(p, 2 * p + 1)
            assert l ** p < k ** (p - 1), p
    log("all Q = 2p+1 prime-power cases with 23 <= p <= 293 break: OK")
    log(elapsed())

    section("SUMMARY")
    log("All assertions passed.  k = 299593, l = 48913, l^7 < k^6 (ratio 0.92636), |G_7| = 100663297, s_7 = 2^21.")
    log("total time " + elapsed())

if __name__ == "__main__":
    try:
        main()
    finally:
        try:
            import os
            here = os.path.dirname(os.path.abspath(__file__))
            with open(os.path.join(here, "verify_out.txt"), "w", encoding="utf-8") as fh:
                fh.write("\n".join(OUT) + "\n")
        except Exception as e:      # pragma: no cover
            print("could not write output file:", e)
