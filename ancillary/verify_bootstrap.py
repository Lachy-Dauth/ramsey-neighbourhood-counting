"""Independent exact arithmetic checker for bootstrap tables.

No convex-hull optimizer is imported.  Every proposed supporting line is
checked at every integer degree.  Mathematical premises are documented in
README.md; this checker verifies the finite arithmetic certificate, not a
Lean proof of those graph-theoretic premises.
"""
import json
from fractions import Fraction
from pathlib import Path

HERE=Path(__file__).resolve().parent
x=json.loads((HERE/'tables.json').read_text())
UPPER={int(k):v for k,v in x['upper'].items()}
TABLE={int(k):{int(n):v for n,v in t.items()} for k,t in x['tables'].items()}
LOG={int(k):{int(n):v for n,v in t.items()} for k,t in x['log'].items()}
D={2:2,3:5,4:8,5:13,6:17,7:22,8:27,9:35,10:40,11:49,12:58,13:67,14:76,15:86}
INPUT={1:1,2:6,3:17,4:30,5:57}
def ceil(x):return -((-x.numerator)//x.denominator)
def value(k,n,h,previous_bound):
 # Maximize the two locally allowed opposite-colour edge counts over
 # red and blue degrees, each bounded above by D[k].
 a=max(((k-1)*r)//2+((k-1)*(h-r))//2
       for r in range(max(0,h-D[k]),min(h,D[k])+1))
 correction=3*(k-1)*h-6*a
 U=UPPER[k-2]
 F=3*h*h+(U+5-3*n-3*k)*h+(n-U-1)*(n-1)+correction
 G=h*(2*h-n-3*(k-1))+2*previous_bound[n-1-h]+correction
 return F,G

def support_bound(n,values,cert):
 if len(cert)==1:
  h,v=cert[0]
  assert h==min(values) and values[h]==v and v<=0
  return (n*h+1)//2
 assert len(cert)==4
 a,fa,b,fb=cert
 assert a<b and values[a]==fa and values[b]==fb and fa>0 and fb<=0
 slope=Fraction(fb-fa,b-a)
 intercept=Fraction(fa)-slope*a
 assert slope<0
 assert all(slope*h+intercept<=v for h,v in values.items())
 return ceil(Fraction(n)*intercept/(-2*slope))

assert TABLE[2]=={n:n*(n-1)//2 for n in range(6)}
rows=0;degree_checks=0;conclusions={}
for k in range(3,16):
 assert TABLE[k][0]==0 and TABLE[k][1]==0
 for n in range(2,UPPER[k]):
  assert n in TABLE[k]
  deg=range(max(0,n-UPPER[k-1]),min(2*D[k],n-1)+1)
  vals={h:value(k,n,h,TABLE[k-1]) for h in deg}
  rec=LOG[k][n]
  c={}
  for idx,key in enumerate(['basic','rec']):
   c[key]=support_bound(n,{h:v[idx] for h,v in vals.items()},rec['certs'][key])
  c['delete']=TABLE[k][n-1]+max(0,n-UPPER[k-1])
  c['subset']=max([ceil(Fraction(TABLE[k][s]*n*(n-1),s*(s-1))) for s in range(2,n)]+[0])
  assert c==rec['values'],(k,n,c,rec['values'])
  assert TABLE[k][n]==max(c.values())
  assert TABLE[k][n]<=min(n*D[k],n*(n-1)//2)
  rows+=1;degree_checks+=len(vals)
 if k in INPUT:
  assert UPPER[k]==INPUT[k]
  continue
 n=UPPER[k]
 vals={h:value(k,n,h,TABLE[k-1]) for h in range(max(0,n-UPPER[k-1]),min(2*D[k],n-1)+1)}
 idx=LOG[k][n]['impossible']
 assert idx in (0,1)
 assert vals and all(v[idx]>0 for v in vals.values())
 conclusions[k]={'upper':n,'inequality':'basic' if idx==0 else 'recursive','minimum':min(v[idx] for v in vals.values()),'degrees':[min(vals),max(vals)]}
print(json.dumps({'status':'all exact certificates passed','density_rows':rows,'degree_cases':degree_checks,'conclusions':conclusions},indent=2))
