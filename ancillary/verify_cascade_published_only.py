"""Proposition 6.5 with PUBLISHED two-colour inputs only.

DS1.18 Table Ib reports R(4,6)<=40, R(4,7)<=58, R(4,8)<=79, R(5,6)<=85 as unpublished
(Angeltveit-McKay, personal communication). With the published bounds 41, 61, 84, 87
instead, the same certificates give R(3,4,6)<=276, R(3,4,7)<=458, R(3,4,8)<=705,
R(3,5,5)<=346, R(3,5,6)<=685. Standard library only; reuses verify_cascade.py.
"""
import importlib.util, json
from pathlib import Path
spec = importlib.util.spec_from_file_location("vc", Path(__file__).resolve().parent / "verify_cascade.py")
vc = importlib.util.module_from_spec(spec); spec.loader.exec_module(vc)
vc.TWO.update({(4, 6): 41, (4, 7): 61, (4, 8): 84, (5, 6): 87})
out = [vc.check((3, 4, 6), 276, [-2, 4, 4, 1, 1, -2]), vc.check((3, 4, 7), 458, [2, 2, 2, 2, -1, -1]),
       vc.check((3, 4, 8), 705, [2, 2, 2, 2, -1, -1]), vc.check((3, 5, 5), 346, [-2, 4, 4, 1, 1, -2]),
       vc.check((3, 5, 6), 685, [-2, 4, 4, 1, 1, -2])]
print(json.dumps([{k: r[k] for k in ("target", "bound", "profile_count", "minimum_margin")} for r in out]))
print("published-only certificates passed")
