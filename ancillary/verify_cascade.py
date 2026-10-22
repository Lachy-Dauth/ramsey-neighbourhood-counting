"""Exact, dependency-free verification of subsequent triangle-count bounds.

Published two-colour inputs: Radziszowski DS1 revision 18 (2026), Table Ib.
Other three-colour inputs are listed explicitly, including the separately
proved bounds 88,129,179 and 155. This program does not certify those inputs.
The proof of the triangle identities is also checked on all 27 triangles.
"""
from fractions import Fraction
from itertools import product
from math import comb
import json

TWO={(3,3):6,(3,4):9,(3,5):14,(3,6):18,(3,7):23,(3,8):28,
     (4,4):18,(4,5):25,(4,6):40,(4,7):58,(4,8):79,
     (5,5):46,(5,6):85}
THREE={(3,3,3):17,(3,3,4):30,(3,3,5):57,(3,3,6):88,
       (3,3,7):129,(3,3,8):179,(3,4,4):77,(3,4,5):155,(4,4,4):229}
def ram(t):
    t=tuple(sorted(t))
    if t[0]<=1:return 1
    if t[0]==t[1]==2:return t[2]
    if t[0]==2:return TWO[t[1:]]
    return THREE[t]
def dec(t,*idx):
    t=list(t)
    for i in idx:t[i]-=1
    return t
def data(t):
    return [ram(dec(t,i))-1 for i in range(3)],[[ram(dec(t,i,j))-1 for j in range(3)] for i in range(3)]
PAIRS=[(0,1),(0,2),(1,2)]
def form(d,w):
    return sum(a*comb(v,2) for a,v in zip(w[:3],d))+sum(a*d[i]*d[j] for a,(i,j) in zip(w[3:],PAIRS))
def upper(d,w,A):
    s=sum(max(0,w[i])*(A[i][i]*d[i]//2) for i in range(3))
    for k,(i,j) in enumerate(PAIRS):
        s+=max(0,w[i]+2*w[3+k])*(A[i][j]*d[i]//2)
        s+=max(0,w[j]+2*w[3+k])*(A[i][j]*d[j]//2)
    return s
def verify_triangle_identity(w):
    assert sum(w[3:])<=0 # A negative rainbow term may be discarded in an upper bound.
    for edges in product(range(3),repeat=3):
        d=[[0]*3 for _ in range(3)]
        for (i,j),c in zip(PAIRS,edges):d[i][c]+=1;d[j][c]+=1
        hist=[edges.count(i) for i in range(3)]
        rhs=sum(3*w[i]*int(hist[i]==3) for i in range(3))
        for k,(i,j) in enumerate(PAIRS):
            rhs+=(w[i]+2*w[3+k])*int(hist[i]==2 and hist[j]==1)
            rhs+=(w[j]+2*w[3+k])*int(hist[j]==2 and hist[i]==1)
        rhs+=sum(w[3:])*int(hist==[1,1,1])
        assert sum(form(v,w) for v in d)==rhs

def check(t,n,w):
    D,A=data(t);verify_triangle_identity(w)
    degrees=[(r,b,n-1-r-b) for r in range(max(0,n-1-D[1]-D[2]),D[0]+1) for b in range(max(0,n-1-r-D[2]),D[1]+1) if 0<=n-1-r-b<=D[2]]
    vals=[form(d,w)-upper(d,w,A) for d in degrees]
    assert degrees and min(vals)>0,(t,n,min(vals))
    THREE[t]=min(THREE.get(t,n),n)
    return {'target':t,'bound':n,'degree_caps':D,'double_neighbourhood_caps':A,'coefficients':w,'profile_count':len(degrees),'minimum_margin':min(vals),'minimum_at':degrees[vals.index(min(vals))]}

if __name__=='__main__':
    def unrounded_L(r,b,g):
        return -r*(r-1)+2*b*(b-1)+2*g*(g-1)+r*b+r*g-2*b*g
    def coeffs(f):
        c=f(0,0)
        xx=Fraction(f(2,0)-2*f(1,0)+c,2)
        yy=Fraction(f(0,2)-2*f(0,1)+c,2)
        x=f(1,0)-c-xx;y=f(0,1)-c-yy
        xy=f(1,1)-c-xx-yy-x-y
        return c,x,y,xx,xy,yy
    assert coeffs(lambda x,y:unrounded_L(34+x+y,87-x,154-y)-85*(87-x)-224*(154-y))==(473,187,-76,0,-6,0)
    assert coeffs(lambda x,y:unrounded_L(37+x+y,154-x,154-y)-184*(154-x)-184*(154-y))==(208,76,76,0,-6,0)
    assert min(473+187*x-76*y-6*x*y for x in range(6) for y in range(6-x))==93
    assert min(208+76*x+76*y-6*x*y for x in range(9) for y in range(9-x))==208
    result=[]
    result.append(check((3,4,6),276,[-2,4,4,1,1,-2]))
    # 456 follows from the merged-colour polynomial; a convenient equivalent
    # triangle certificate has equal wedge weights and one positive mixed term.
    result.append(check((3,4,7),456,[2,2,2,2,-1,-1]))
    result.append(check((3,4,8),700,[2,2,2,2,-1,-1]))
    result.append(check((3,5,5),346,[-2,4,4,1,1,-2]))
    result.append(check((3,5,6),683,[-2,4,4,1,1,-2]))
    print(json.dumps({'verified':result,'scope':'Exact certificate arithmetic, conditional on stated Ramsey inputs; no floating-point computation.'},indent=2))
