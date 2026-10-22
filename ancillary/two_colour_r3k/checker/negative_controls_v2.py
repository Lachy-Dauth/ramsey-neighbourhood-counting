"""Negative controls for check_r3k_v2.py: each tampered certificate or weakened
input must be REJECTED.  Usage: negative_controls_v2.py CERT"""
import json, sys, subprocess, copy, os, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
CHK = os.path.join(HERE, 'check_r3k_v2.py')
cert = json.load(open(sys.argv[1]))

def run(c, extra=()):
    with tempfile.NamedTemporaryFile('w', suffix='.json', delete=False) as f:
        json.dump(c, f); p = f.name
    r = subprocess.run([sys.executable, CHK, p] + list(extra), capture_output=True, text=True)
    os.unlink(p)
    return r.returncode, (r.stdout.strip().splitlines() or [''])[-1]

def find_seq_rows(c):
    out = []
    for ks, lev in c['levels'].items():
        for i, row in enumerate(lev['rows']):
            if row[2][0] in ('seq', 'seq-infeasible'):
                out.append((ks, i))
    return out

tests = []
# 0: untouched must pass
tests.append(('untouched', cert, []))
# 1: weaken a cited GR13 input (e(3,10,39) 151 -> 150)
tests.append(('input e(3,10,39)=150', cert, ['--override', '10,39,150']))
# 2: drop Backelin inputs
if 'back3' in cert.get('uses', []):
    tests.append(('no back3', cert, ['--no-back3']))
else:
    tests.append(('robust: no back3 (not used)', cert, ['--no-back3']))
seqrows = find_seq_rows(cert)
ks, i = seqrows[0]
# 3: corrupt one Farkas multiplier (first 'lp' cert found)
c3 = copy.deepcopy(cert); done = False
for ks2, i2 in seqrows:
    excl = c3['levels'][ks2]['rows'][i2][2][4]
    for e, lst in excl.items():
        for item in lst:
            if item[1][0] == 'lp':
                item[1][1][0][1] = str(-1 * eval(item[1][1][0][1].replace('/', '*1.0/')) * 3) if False else '0'
                done = True; break
        if done: break
    if done: break
tests.append(('zeroed Farkas multiplier', c3, []))
# 4: remove one sequence certificate
c4 = copy.deepcopy(cert)
excl = c4['levels'][ks]['rows'][i][2][4]
e0 = sorted(excl, key=int)[0]
excl[e0] = excl[e0][1:]
tests.append(('missing sequence certificate', c4, []))
# 5: raise a value by one beyond its justification (the row after a seq row)
c5 = copy.deepcopy(cert)
row = c5['levels'][ks]['rows'][i]
if row[1] is not None:
    row[1] += 1
tests.append(('seq row value +1', c5, []))
# 6: claim one better than proved
B16 = cert['levels']['16']['B']
tests.append((f'claim R(3,16)<={B16-1}', cert, ['--claim', f'16,{B16-1}']))
# 7: R(3,10) <= 42 with e(3,10,41) >= 120 (GR13 has 172): must reject
tests.append(('R(3,10)<=42, e(3,10,41)>=120', cert, ['--r310', '42', '--override', '10,41,120']))
# 8: robustness (expected ACCEPT): R(3,10) <= 42 with GR13's e(3,10,41) >= 172
tests.append(('robust: R(3,10)<=42', cert, ['--r310', '42']))
ok = True
for name, c, extra in tests:
    rc, last = run(c, extra)
    expect = 0 if (name == 'untouched' or name.startswith('robust')) else 1
    status = 'as expected' if (rc == 0) == (expect == 0) else 'UNEXPECTED'
    if status != 'as expected': ok = False
    print(f'{name:35s} rc={rc}  {status}   | {last[:110]}')
print('ALL NEGATIVE CONTROLS BEHAVE' if ok else 'SOME CONTROL FAILED')
sys.exit(0 if ok else 1)
