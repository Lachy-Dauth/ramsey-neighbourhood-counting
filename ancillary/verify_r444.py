"""Exact check of Lemma 7.3, Theorem 7.4 (R(4,4,4)<=226) and identity (7) (R(4,4,4)<=225).

Standard library only. Every density is the average over all 24 vertex relabellings and
6 colour relabellings of a labelled colouring of K4; an identity among symmetrised densities
holds for every colouring of K_n iff it holds for each of the 729 labelled colourings of K4.
Run: python3 verify_r444.py   (a few seconds)
"""
# Independent check of the R(4,4,4) <= 226 and <= 225 certificates (fresh implementation).
from fractions import Fraction as Fr
from itertools import product, permutations
E=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
idx={e:i for i,e in enumerate(E)}
def col(c,i,j): return c[idx[(min(i,j),max(i,j))]]
R,B,G=0,1,2
VP=list(permutations(range(4))); CP=list(permutations(range(3)))
def density(event):
    """map colouring -> symmetrised probability of event (fraction over 24*6 relabellings)"""
    out={}
    for c in product(range(3),repeat=6):
        cnt=0
        for p in VP:
            for q in CP:
                # relabelled colouring: vertex i -> p[i], colour x -> q[x]
                d=lambda i,j: q[col(c,p[i],p[j])]
                cnt+=event(d)
        out[c]=Fr(cnt,144)
    return out
ev={
 's':lambda d: d(0,1)==d(0,2)==d(0,3)==R,
 't':lambda d: d(0,1)==R and d(0,2)==B and d(0,3)==G,
 'x':lambda d: d(0,1)==d(0,2)==R and d(0,3)==B,
 'm':lambda d: d(0,1)==d(0,2)==d(1,2)==R,
 'b':lambda d: d(0,1)==d(0,2)==R and d(1,2)==B,
 'A':lambda d: d(0,1)==d(0,2)==d(1,2)==d(0,3)==R,
 'B':lambda d: d(0,1)==d(0,2)==d(1,2)==d(0,3)==R and d(1,3)==B,
 'C':lambda d: d(0,1)==d(0,2)==d(0,3)==d(1,3)==R and d(1,2)==B,
 'D':lambda d: d(0,1)==d(0,2)==d(0,3)==R and d(1,2)==B and d(1,3)==G,
 'E':lambda d: d(0,1)==d(0,3)==d(1,3)==R and d(0,2)==d(1,2)==B,
 'X':lambda d: d(0,1)==d(0,2)==d(0,3)==R and d(1,2)==d(1,3)==B,
 'Y':lambda d: d(0,1)==d(0,2)==d(1,2)==R and d(0,3)==B and d(1,3)==G,
}
D={k:density(f) for k,f in ev.items()}
cols=list(D['s'].keys())
def report(label,cond):
    assert cond, label
    print(label,"OK")
def holds(fn): return all(fn({k:D[k][c] for k in D})==0 for c in cols)
assert_all=[]
report("B==C:",holds(lambda v:v['B']-v['C']))
report("(I)  9m+18b = 1+6s-6t:",holds(lambda v:9*v['m']+18*v['b']-1-6*v['s']+6*v['t']))
report("(II) 3A+6B+6D+6E = 2s+m:",holds(lambda v:3*v['A']+6*v['B']+6*v['D']+6*v['E']-2*v['s']-v['m']))
report("(II') 2X+Y = D+2E:",holds(lambda v:2*v['X']+v['Y']-v['D']-2*v['E']))
lhs=lambda v:Fr(-2189,180630)+Fr(7846,30105)*v['s']+Fr(2189,30105)*v['t']
rhs=lambda v:(v['A']-Fr(74,223)*v['m'])/2+Fr(38,45)*(v['B']-Fr(29,223)*v['m'])+Fr(7,45)*(v['C']-Fr(17,223)*v['b'])+(v['D']-Fr(29,223)*v['b'])+(v['E']-Fr(17,223)*v['b'])
report("226 identity:",holds(lambda v:lhs(v)-rhs(v)))
# orbits
seen=set();orbits=[]
for c in cols:
    if c in seen: continue
    orb=set()
    for p in VP:
        for q in CP:
            orb.add(tuple(q[col(c,p[i],p[j])] for (i,j) in E))
    seen|=orb; orbits.append((c,len(orb)))
assert len(orbits)==15 and sum(o[1] for o in orbits)==729; print("orbits:",len(orbits),sorted(o[1] for o in orbits))
# per-vertex check 226
Dn=225*224*223
for p in [(73,76,76),(74,75,76),(75,75,75)]:
    mono=Fr(sum(d*(d-1)*(d-2) for d in p),Dn); rain=Fr(6*p[0]*p[1]*p[2],Dn)
    s=mono/3; t=rain/6
    assert lhs({'s':s,'t':t})>0, p; print(p,"LHS(226) at vertex:",lhs({'s':s,'t':t}),"> 0 OK")

# ---- R(4,4,4) <= 225 ----
def a(i,j):
    if (i,j) in [(R,B),(B,R),(G,G)]: return -1
    if (i,j) in [(R,G),(B,B),(G,R)]: return 1
    return 0
T={'RRR':(R,R,R),'RRB':(R,R,B),'RBR':(R,B,R),'RBB':(R,B,B),'RBG':(R,B,G)}
rows=[('RRR',{(0,3):R,(1,3):R},16,12580),('RRB',{(0,3):R,(1,3):R},17,70744),('RRB',{(0,3):R,(1,3):G},29,45584),
      ('RBR',{(0,3):R},75,40848),('RBR',{(0,3):R,(1,3):B},29,40848),('RBB',{(0,3):R,(1,3):R},17,96644),
      ('RBG',{(0,3):R,(1,3):B},29,40848),('RBG',{(0,3):R,(1,3):G},29,142968)]
def tri(d,t): return (d(0,1),d(0,2),d(1,2))==T[t]
ev={}
for k,(t,F,q,w) in enumerate(rows):
    ev[f'pTF{k}']=(lambda t,F:(lambda d: tri(d,t) and all(d(*e)==c for e,c in F.items())))(t,F)
    ev[f'pT{k}']=(lambda t:(lambda d: tri(d,t)))(t)
ev['s']=lambda d: d(0,1)==d(0,2)==d(0,3)==R
ev['x']=lambda d: d(0,1)==d(0,2)==R and d(0,3)==B
ev['t']=lambda d: d(0,1)==R and d(0,2)==B and d(0,3)==G
ev['Q1']=lambda d: (d(0,1)==R)*a(d(0,2),d(1,2))*a(d(0,3),d(1,3))
ev['Q2']=lambda d: (d(0,1)==R)*a(d(0,2),d(1,2))**2
Dn={k:density(f) for k,f in ev.items()}
ok=True
for c in Dn['s']:
    v={k:Dn[k][c] for k in Dn}
    L=[v[f'pTF{k}']-Fr(q,222)*v[f'pT{k}'] for k,(t,F,q,w) in enumerate(rows)]
    Q=Fr(222,223)*v['Q1']+Fr(1,223)*v['Q2']
    lhs=Fr(35020,3)*v['s']+Fr(39040,3)*v['x']-24012*v['t']
    rhs=sum(w*l for (t,F,q,w),l in zip(rows,L))-5129*Q
    ok&=(lhs==rhs)
assert ok, "225 identity"; print("225 identity holds on all 729: OK")
for p in [(72,76,76),(73,75,76),(74,74,76),(74,75,75)]:
    S1=sum(d*(d-1)*(d-2) for d in p); S2=sum(p[i]*(p[i]-1)*p[j] for i in range(3) for j in range(3) if i!=j)
    J=70040*S1+39040*S2-432216*p[0]*p[1]*p[2]
    assert J>0, p; print(p,"J =",J,"> 0 OK")
