from fractions import Fraction as F
from math import ceil
import json
from pathlib import Path

def envelope(n,vals):
 if not vals or min(vals.values())>0:return None,None
 hull=[]
 for h,v in sorted(vals.items()):
  while len(hull)>=2 and (hull[-1][1]-hull[-2][1])*(h-hull[-1][0]) >= (v-hull[-1][1])*(hull[-1][0]-hull[-2][0]):hull.pop()
  hull.append((h,v))
 root=F(hull[0][0]); cert=[hull[0]]
 if hull[0][1]>0:
  for (a,fa),(b,fb) in zip(hull,hull[1:]):
   if fa>0 and fb<=0:
    root=F(a)+F(fa*(b-a),fa-fb);cert=[a,fa,b,fb];break
  else:raise ValueError(hull)
 return ceil(n*root/2),cert

def cap(k,r):
 return ((k-1)*r)//2

def bounds(n,k,d,child,u2,prev,mtable):
 hi=min(2*d,n-1);lo=max(0,n-prev)
 vals={}
 for h in range(lo,hi+1):
  z=n-1-h
  if z not in child:continue
  a=max(cap(k,r)+cap(k,h-r) for r in range(max(0,h-d),min(h,d)+1))
  p=3*(k-1)*h-6*a
  vals[h]=[3*h*h+(u2+5-3*n-3*k)*h+(n-u2-1)*(n-1)+p,
   h*(2*h-n-3*(k-1))+2*child[z]+p]
 candidates={}
 certs={}
 for idx in range(2):
  b,c=envelope(n,{h:v[idx] for h,v in vals.items()})
  if b is None:return None,{'impossible':idx,'vals':vals}
  candidates['basic' if idx==0 else 'rec']=b;certs['basic' if idx==0 else 'rec']=c
 if n-1 in mtable:
  candidates['delete']=mtable[n-1]+max(0,n-prev)
 # Induced-subset averaging: E>=m_s *n(n-1)/(s(s-1)).
 candidates['subset']=max([ceil(F(m*n*(n-1),s*(s-1))) for s,m in mtable.items() if s>=2]+[0])
 out=max(candidates.values())
 if out>min(n*d,n*(n-1)//2):return None,{'impossible':'edges','vals':vals,'candidates':candidates}
 return out,{'values':candidates,'certs':certs}

def run():
 d={2:2,3:5,4:8,5:13,6:17,7:22,8:27,9:35,10:40,11:49,12:58,13:67,14:76,15:86}
 u={1:1,2:6,3:17,4:30,5:57}
 tables={2:{n:n*(n-1)//2 for n in range(6)}};log={}
 for k in range(3,16):
  if k not in u:u[k]=2*d[k]+u[k-1]+1
  table={0:0,1:0};kl={}
  for n in range(2,u[k]):
   b,c=bounds(n,k,d[k],tables[k-1],u[k-2],u[k-1],table)
   kl[n]=c
   if b is None:
    u[k]=n;break
   table[n]=b
  tables[k]=table;log[k]=kl
  print('k',k,'upper',u[k],'last',list(table.items())[-6:],flush=True)
 (Path(__file__).resolve().parent/'tables.json').write_text(json.dumps({'upper':u,'tables':tables,'log':log},indent=1))
if __name__=='__main__':run()
