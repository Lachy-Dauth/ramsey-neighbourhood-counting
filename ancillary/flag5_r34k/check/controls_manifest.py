#!/usr/bin/env python3
"""Negative controls (controls_flag5.negative) for every certificate of a manifest, each with exactly the inputs
listed for it in the manifest.  Usage: controls_manifest.py ../certificates/manifest.json [cert names ...]
For each certificate: unchanged -> VALID; a row constant edited, the same certificate at n-1, the stored degree
caps edited, and (if it uses new inputs) the base inputs only -> INVALID; the single-term perturbations (largest
row multipliers x 9/10, largest square lambda x 11/10 or removed) are reported and at least one must be rejected."""
import json, os, sys
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
import controls_flag5 as CF


def main(path, only):
    man = json.load(open(path)); base = os.path.dirname(os.path.abspath(path)); ok = True
    for e in man:
        if e.get('checker') == 'lemma2.1' or (only and e['cert'] not in only):
            continue
        extra = {tuple(sorted(int(x) for x in k.split(','))): int(v) for k, v in e['inputs'].items()}
        print(f"Negative controls on {e['cert']} (R{tuple(e['t'])} <= {e['n']} [{e.get('chain', 'U')}]) with inputs {extra or 'base'}", flush=True)
        ok &= CF.negative(os.path.join(base, e['cert']), extra)
    print('ALL CONTROLS PASSED' if ok else 'SOME CONTROL FAILED')
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1], sys.argv[2:]) else 1)
