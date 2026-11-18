#!/usr/bin/env python3
"""Independent, arbitrary-weight CGG four-corner complexes over QQ."""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product,combinations
from math import comb
from flint import fmpq,fmpq_mat

def add(p,u,a):
    if a:
        p[u]=p.get(u,Q(0))+a
        if not p[u]:del p[u]

class Corner:
    def __init__(self,j,r,s=1):
        self.j,self.r,self.m,self.s=j,r,2*j+r,Q(s)
        assert self.m>=3
        self.objects=(0,1,self.m,self.m+1)
        self.d=self.m+r+1
        self.P={(j-k,2*k,j-k+r,0):Q((-1)**k*comb(j,k)) for k in range(j+1)}
        self.fields=[{},{(1,0,0,0):Q(1)},{(0,1,0,0):Q(2)},{u:-a for u,a in self.P.items()}]

    @lru_cache(None)
    def basis(self,degree):
        ans=[]
        for w in range(degree//self.m+1):
            rem=degree-self.m*w
            for x in range(rem+1):
                for y in range(rem-x+1):ans.append((x,y,rem-x-y,w))
        return tuple(ans)

    def N(self,p):
        ans={}
        for u,a in p.items():
            for i,n in enumerate(u):
                if n:
                    z=list(u);z[i]-=1
                    for v,b in self.fields[i].items():add(ans,tuple(v[k]+z[k] for k in range(4)),a*b*n)
        return ans

    @lru_cache(None)
    def mono(self,a,b):
        weight=b[1]+2*b[2]+self.d*b[3]
        p={a:Q(1)};ans={};choose=Q(1);power=Q(1);n=0
        while p:
            for u,c in p.items():add(ans,tuple(u[k]+b[k] for k in range(4)),power*choose*c)
            n+=1;choose*=Q(weight-n+1,n);power*=self.s;p=self.N(p)
        return ans

    @lru_cache(None)
    def cochains(self,n,kind):
        ans=[]
        for chain in combinations(self.objects,n+1):
            for ins in product(*(self.basis(chain[k+1]-chain[k]) for k in range(n))):
                iw=sum(a[3] for a in ins)
                for out in self.basis(chain[-1]-chain[0]):
                    keep=(out[3]>iw if kind=='Q' else
                          iw>0 if kind=='K' else
                          iw==0 and out[3]==0 if kind=='N' else
                          out[3]<=iw if kind=='F' else True)
                    if keep:ans.append((chain,ins,out))
        return tuple(ans)

    def differential(self,n,kind):
        source=self.cochains(n,kind);target=self.cochains(n+1,kind)
        cols={c:i for i,c in enumerate(source)};rows={c:i for i,c in enumerate(target)}
        ans=fmpq_mat(len(target),len(source))
        def put(row,col,val):
            i=rows.get(row);k=cols.get(col)
            if i is not None and k is not None and val:ans[i,k]+=fmpq(val.numerator,val.denominator)
        for chain in combinations(self.objects,n+2):
            for ins in product(*(self.basis(chain[k+1]-chain[k]) for k in range(n+1))):
                tail=chain[1:];head=chain[:-1]
                for v in self.basis(tail[-1]-tail[0]):
                    for out,c in self.mono(ins[0],v).items():put((chain,ins,out),(tail,ins[1:],v),c)
                for i in range(1,n+1):
                    short=chain[:i]+chain[i+1:]
                    for v,c in self.mono(ins[i-1],ins[i]).items():
                        si=ins[:i-1]+(v,)+ins[i+1:]
                        for out in self.basis(chain[-1]-chain[0]):put((chain,ins,out),(short,si,out),(-1)**i*c)
                for v in self.basis(head[-1]-head[0]):
                    for out,c in self.mono(v,ins[-1]).items():put((chain,ins,out),(head,ins[:-1],v),(-1)**(n+1)*c)
        return ans

    def ranks(self,kind):
        a=self.differential(1,kind);b=self.differential(2,kind)
        assert a.nrows()==b.ncols()
        assert b*a==fmpq_mat(b.nrows(),a.ncols())
        dims=[len(self.cochains(i,kind)) for i in (1,2,3)]
        ranks=[a.rank(),b.rank()]
        return {'m':self.m,'j':self.j,'r':self.r,'s':str(self.s),'kind':kind,'dimensions':dims,'ranks':ranks,'cohomology':[dims[0]-ranks[0],dims[1]-sum(ranks),dims[2]-ranks[1]]}
