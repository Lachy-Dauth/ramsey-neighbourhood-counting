"""Extra negative controls for high levels (k >= 24) of a v2 certificate."""
import json, sys, copy, subprocess, tempfile, os
HERE = os.path.dirname(os.path.abspath(__file__))
cert = json.load(open(sys.argv[1]))
def run(c, extra=()):
    with tempfile.NamedTemporaryFile('w', suffix='.json', delete=False) as f:
        json.dump(c, f); p = f.name
    r = subprocess.run([sys.executable, os.path.join(HERE, 'check_r3k_v2.py'), p] + list(extra), capture_output=True, text=True)
    os.unlink(p); return r.returncode, r.stdout.strip().splitlines()[-1]
tests = []
# (a) claim R(3,24) one below the certified cap by truncating level 24 (drop last row, mark previous as cap)
c = copy.deepcopy(cert); lev = c['levels']['24']; B = lev['B']
lev['rows'] = lev['rows'][:-1]; lev['rows'][-1] = [B - 1, None, lev['rows'][-1][2] if lev['rows'][-1][2][0] in ('infeasible',) else ['infeasible']]
lev['B'] = B - 1
tests.append((f'cap R(3,24)<={B-1} forged', c, []))
# (b) bump an 'edge' row at level 30 by one
c = copy.deepcopy(cert)
for row in c['levels']['30']['rows']:
    if row[2][0] == 'edge':
        last = row
row = [r for r in c['levels']['30']['rows'] if r[2][0] == 'edge'][-1]; row[1] += 1
tests.append(('level-30 edge row +1', c, []))
# (c) bump an 'edge' row at level 45 by one
c = copy.deepcopy(cert)
row = [r for r in c['levels']['45']['rows'] if r[2][0] == 'edge'][-1]; row[1] += 1
tests.append(('level-45 edge row +1', c, []))
# (d) weaken GR13 input e(3,10,40) 161 -> 160
tests.append(('input e(3,10,40)=150', cert, ['--override', '10,40,150']))
ok = True
for name, c, extra in tests:
    rc, last = run(c, extra)
    ok &= rc == 1
    print(f'{name:32s} rc={rc} {"as expected" if rc == 1 else "UNEXPECTED"} | {last[:100]}')
print('ALL HIGH-LEVEL CONTROLS REJECTED' if ok else 'SOME CONTROL FAILED')
sys.exit(0 if ok else 1)
