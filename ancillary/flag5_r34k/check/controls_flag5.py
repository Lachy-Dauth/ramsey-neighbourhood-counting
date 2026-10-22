#!/usr/bin/env python3
"""Controls for check_flag5_mix.py.

Positive (soundness) controls on explicit t-avoiding colourings of K_m (vertex subsets of circulant colourings,
which are irregular, so many profiles occur).  With the CHECKER'S OWN term functions (build_terms at n = m):
  * every 'up', 'low', 'int' row (all kinds, all J and a, at every 4-root pattern rho that occurs, or a random
    sample of them) has expectation <= 0 under the exact law of the labelled 5-pattern;
  * the star term has expectation exactly (1/m) sum_v mean_sigma J(sigma d(v)) (random integer multipliers);
  * every square term has expectation exactly lam E_r[1_tau (sum_b v_b f_b(r))^2], the right side computed by
    brute force over root tuples r and ordered e-tuples (random integer v), for k0 = 1, 2, 3.
Negative controls: perturbed certificates must be rejected.
Usage: controls_flag5.py [cert.json ...] [--input 3,4,4:74 ...] [--skip-positive]
"""
import json, sys, os, copy, random, itertools, tempfile
from fractions import Fraction as Fr
from collections import Counter
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, here)
import check_flag5_mix as C

PAIRS = C.PAIRS


def avoiding(m, colf, t):
    for c in range(3):
        k = t[c]
        def ext(cl, cand):
            if len(cl) == k:
                return True
            for v in cand:
                if all(colf(v, u) == c for u in cl):
                    if ext(cl + [v], [w for w in cand if w > v]):
                        return True
            return False
        if ext([], list(range(m))):
            return False
    return True


def law5(m, colf, Gt):
    cnt = Counter()
    for xs in itertools.permutations(range(m), 5):
        key = tuple(colf(xs[i], xs[j]) for (i, j) in PAIRS)
        cnt[key] += 1
    out = Counter()
    for key, w in cnt.items():
        for s in Gt:
            out[tuple(s[c] for c in key)] += w
    tot = sum(out.values())
    return {k: Fr(v, tot) for k, v in out.items()}


def positive(t, m, colf, label, rnd, max_rho=None):
    Gt = [s for s in itertools.permutations(range(3)) if all(t[s[c]] == t[c] for c in range(3))]
    assert avoiding(m, colf, t), 'not t-avoiding'
    lw = law5(m, colf, Gt)
    base = dict(t=list(t), n=m, stars=[], rows=[], squares=[])
    B0 = C.build_terms(base)
    prof = [tuple(sum(1 for u in range(m) if u != v and colf(u, v) == c) for c in range(3)) for v in range(m)]
    assert all(p in B0['profs'] for p in prof), 'a vertex profile is not admissible'
    # rows
    byrho = {}
    for p, w in lw.items():
        byrho.setdefault(p[:3] + (p[4], p[5], p[7]), []).append((p, w))   # pairs 01,02,03,12,13,23
    rhos = sorted(byrho)
    if max_rho and len(rhos) > max_rho:
        rhos = rnd.sample(rhos, max_rho)
    worst = None; nrows = 0
    specs = [('up', (j,), (c,)) for j in range(4) for c in range(3)] + [('low', (j,), (c,)) for j in range(4) for c in range(3)]
    specs += [('int', J, a) for r in (1, 2, 3, 4) for J in itertools.combinations(range(4), r) for a in itertools.product(range(3), repeat=r)]
    for rho in rhos:
        for kind, J, a in specs:
            try:
                q = B0['row_q'](kind, rho, J, a)
            except AssertionError:
                continue
            cert = copy.deepcopy(base)
            cert['rows'] = [dict(kind=kind, rho=list(rho), J=list(J), a=list(a), q=q, mult='1')]
            F = C.build_terms(cert)['F']
            e = sum(w * F(p) for p, w in byrho[rho])
            nrows += 1
            worst = e if worst is None or e > worst else worst
    # stars
    ys = {s: rnd.randint(-50, 50) for s in itertools.product(range(3), repeat=4)}
    cert = copy.deepcopy(base); cert['stars'] = [dict(star=list(s), mult=str(v)) for s, v in ys.items()]
    B = C.build_terms(cert)
    lhs = sum(w * B['F'](p) for p, w in lw.items())
    rhs = sum(sum(B['J'](tuple(p[s.index(k)] for k in range(3))) for s in Gt) / len(Gt) for p in prof) / m
    star_ok = lhs == rhs
    # squares
    sq_ok = True; nsq = 0
    def keyof(cf, r, Y, k0):
        k = []
        for y in Y:
            for x in r:
                k.append(cf(x, y))
        for i in range(len(Y)):
            for j in range(i + 1, len(Y)):
                k.append(cf(Y[i], Y[j]))
        return tuple(k)
    for k0, es in ((1, (0, 1, 2)), (2, (0, 1)), (3, (0, 1))):
        taus = sorted(set(tuple(p[C.PIDX[(i, j)]] for i, j in itertools.combinations(range(k0), 2)) for p in lw))
        for tau in rnd.sample(taus, min(3, len(taus))):
            basis = []
            for e in es:
                ln = e * k0 + e * (e - 1) // 2
                for kk in itertools.product(range(3), repeat=ln):
                    basis.append((e,) + kk)
            vec = [rnd.randint(-5, 5) for _ in basis]
            cert = copy.deepcopy(base)
            cert['squares'] = [dict(k0=k0, tau=list(tau), basis=[list(b) for b in basis], lam='1', vec=vec)]
            F = C.build_terms(cert)['F']
            lhs = -sum(w * F(p) for p, w in lw.items())
            vd = dict(zip(basis, vec))
            tot = Fr(0); cntr = 0
            for s in Gt:
                cf = lambda u, v, s=s: s[colf(u, v)]
                for r in itertools.permutations(range(m), k0):
                    cntr += 1
                    if tuple(cf(r[i], r[j]) for i, j in itertools.combinations(range(k0), 2)) != tau:
                        continue
                    others = [y for y in range(m) if y not in r]
                    val = Fr(0)
                    for e in es:
                        num = 0; cnt = 0
                        for Y in itertools.permutations(others, e):
                            num += vd.get((e,) + keyof(cf, r, Y, k0), 0); cnt += 1
                        val += Fr(num, cnt)
                    tot += val * val
            rhs = tot / cntr
            nsq += 1
            sq_ok &= (lhs == rhs) and lhs >= 0
    ok = worst <= 0 and star_ok and sq_ok
    print(f'  {label}: m={m} t={t}, {len(set(prof))} distinct profiles, {len(rhos)} root patterns, {nrows} rows, '
          f'max E[row] = {float(worst):.3e}; star identity {"exact" if star_ok else "FAILS"}; {nsq} squares '
          f'{"exact and >= 0" if sq_ok else "FAIL"} -> {"OK" if ok else "FAIL"}', flush=True)
    return ok


def negative(path, extra):
    cert = json.load(open(path))
    fd, tmp = tempfile.mkstemp(prefix='flag5_control_', suffix='.json'); os.close(fd); out = []; sens = []
    def run(c, label, expect_valid=False, sensitivity=False, ex=None):
        json.dump(c, open(tmp, 'w'))
        try:
            v = C.check(tmp, extra if ex is None else ex, verbose=False)
        except (AssertionError, KeyError):
            v = False
        if sensitivity:
            sens.append(not v)
            print(f'  {label}: {"VALID (slack in this term)" if v else "INVALID -> rejected"}', flush=True); return
        good = v == expect_valid; out.append(good)
        print(f'  {label}: {"VALID" if v else "INVALID"} -> {"OK" if good else "CONTROL FAILED"}', flush=True)
    run(cert, 'unchanged', True)
    big = sorted(range(len(cert['rows'])), key=lambda i: -Fr(cert['rows'][i]['mult']))[:3]
    for i in big:
        c = copy.deepcopy(cert); c['rows'][i]['mult'] = str(Fr(c['rows'][i]['mult']) * Fr(9, 10))
        run(c, f'row {i} ({c["rows"][i]["kind"]}) multiplier x 9/10', sensitivity=True)
    bs = max(range(len(cert['squares'])), key=lambda i: Fr(cert['squares'][i]['lam']))
    c = copy.deepcopy(cert); c['squares'][bs]['lam'] = str(Fr(c['squares'][bs]['lam']) * Fr(11, 10))
    run(c, 'largest square lambda x 11/10', sensitivity=True)
    c = copy.deepcopy(cert); c['squares'] = [s for i, s in enumerate(c['squares']) if i != bs]
    run(c, 'largest square removed', sensitivity=True)
    c = copy.deepcopy(cert); c['rows'][big[0]]['q'] += 1
    run(c, 'a row constant edited (+1)')
    c = copy.deepcopy(cert); c['n'] = cert['n'] - 1; c.pop('D', None)
    run(c, f'same certificate at n-1 = {cert["n"]-1}')
    c = copy.deepcopy(cert); c['D'] = [x - 1 for x in cert['D']]
    run(c, 'stored degree caps edited')
    if extra:
        c = copy.deepcopy(cert); c.pop('D', None)
        run(c, 'base inputs only (new inputs dropped)', ex={})
    os.remove(tmp)
    out.append(any(sens))
    print(f'  single-term perturbations rejected: {sum(sens)} of {len(sens)}')
    return all(out)


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser(); ap.add_argument('certs', nargs='*'); ap.add_argument('--input', action='append', default=[])
    ap.add_argument('--skip-positive', action='store_true'); ap.add_argument('--m', type=int, default=17)
    ap.add_argument('--max-rho', type=int, default=60)
    args = ap.parse_args()
    extra = {}
    for item in args.input:
        k, v = item.split(':'); extra[tuple(sorted(int(x) for x in k.split(',')))] = int(v)
    rnd = random.Random(11)
    pos = True
    if not args.skip_positive:
        print('Positive controls (explicit colourings, checker term functions):', flush=True)
        for t, fn in [((3, 4, 4), 'circ_344.json'), ((3, 4, 5), 'circ_345.json')]:
            circ = json.load(open(os.path.join(here, '..', 'data', fn)))
            colv = circ['30']; M = 30
            colf = lambda u, v, colv=colv: colv[(v - u) % M - 1]
            for trial in range(2):
                keep = sorted(rnd.sample(range(M), args.m))
                colg = lambda u, v, keep=keep, colf=colf: colf(keep[u], keep[v])
                pos &= positive(t, len(keep), colg, f'circulant(30) on {args.m} random vertices', rnd, args.max_rho)
        # a (3,4,5)-colouring is also (3,4,6)- and (3,5,5)-avoiding: test the general-t code paths
        circ = json.load(open(os.path.join(here, '..', 'data', 'circ_345.json'))); colv = circ['30']
        colf = lambda u, v, colv=colv: colv[(v - u) % 30 - 1]
        keep = sorted(rnd.sample(range(30), args.m))
        colg = lambda u, v, keep=keep, colf=colf: colf(keep[u], keep[v])
        pos &= positive((3, 5, 5), len(keep), colg, 'circulant (3,4,5;30) on random vertices, as (3,5,5)', rnd, args.max_rho)
    neg = True
    for p in args.certs:
        print('Negative controls on', p, 'with inputs', extra or 'base', flush=True)
        neg &= negative(p, extra)
    print('ALL CONTROLS PASSED' if pos and neg else 'SOME CONTROL FAILED')
    sys.exit(0 if pos and neg else 1)
