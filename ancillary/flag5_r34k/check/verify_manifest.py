#!/usr/bin/env python3
"""Run the exact checkers on every certificate listed in a manifest, with exactly the inputs listed there, and
check that every input used is either a base value or a bound proved by an earlier entry of the manifest
(or by Lemma 2.1 from such bounds, entries with "method": "lemma2.1"), or an explicitly named starred input.
Usage: verify_manifest.py manifest.json
Manifest entries: {"t": [3,4,5], "n": 137, "cert": "certs/....json", "checker": 4|5|"lemma2.1",
                   "inputs": {"3,4,4": 73, ...}, "chain": "U"|"S"}
For "lemma2.1" entries the claim R(t) <= n is checked as n = sum_i (R(t - e_i) - 1) + 2 from the inputs."""
import json, sys, os, importlib
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
import check_flag4_mix as C4
import check_flag5_mix as C5

STARRED = {(4, 6): 40, (4, 7): 58, (4, 8): 79, (5, 6): 85}     # unpublished AM bounds (paper's starred inputs)


def key(s):
    return tuple(sorted(int(x) for x in s.split(',')))


def main(path):
    man = json.load(open(path)); base = os.path.dirname(os.path.abspath(path))
    proved = {'U': {}, 'S': {}}          # chain -> (t sorted) -> best n proved so far
    allok = True
    for e in man:
        t = tuple(e['t']); n = int(e['n']); chain = e.get('chain', 'U')
        inputs = {key(k): int(v) for k, v in e['inputs'].items()}
        # provenance of inputs
        prov = []
        for k, v in inputs.items():
            if len(k) == 2:
                ok = STARRED.get(k) == v and chain == 'S'
                prov.append(f'R{k}<={v} starred' if ok else f'R{k}<={v} UNJUSTIFIED')
            else:
                avail = [proved['U'].get(k, 10 ** 9)] + ([proved['S'].get(k, 10 ** 9)] if chain == 'S' else [])
                if min(avail) <= v:
                    prov.append(f'R{k}<={v} (entry above)')
                    ok = True
                else:
                    ok = False; prov.append(f'R{k}<={v} UNJUSTIFIED')
            allok &= ok
        if e['checker'] == 'lemma2.1':
            R = C4.make_ramsey(inputs)
            D = [R([t[k] - (k == i) for k in range(3)]) - 1 for i in range(3)]
            res = (n == sum(D) + 2)
            print(f'R{t} <= {n} [{chain}] by Lemma 2.1: D = {D}, sum D + 2 = {sum(D) + 2} -> {"OK" if res else "FAIL"}; inputs: {"; ".join(prov)}')
        else:
            C = C4 if int(e['checker']) == 4 else C5
            cert = json.load(open(os.path.join(base, e['cert'])))
            assert tuple(cert['t']) == t and int(cert['n']) == n
            print(f'R{t} <= {n} [{chain}] by {e["cert"]} ({e["checker"]}-vertex); inputs: {"; ".join(prov) or "base only"}')
            res = C.check(os.path.join(base, e['cert']), inputs)
        allok &= bool(res)
        if res:
            k = tuple(sorted(t))
            proved[chain][k] = min(n, proved[chain].get(k, 10 ** 9))
    print('MANIFEST VERIFIED' if allok else 'MANIFEST HAS FAILURES')
    return allok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1]) else 1)
