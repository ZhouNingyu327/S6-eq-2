"""Independent exact-rational verifier; no imports from the generator.

Reconstructs the dyadic subdivision and recomputes every exclusion with
Fraction intervals (no fixed precision or floating arithmetic).
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,time

class I:
    def __init__(self,lo,hi=None):
        self.lo=F(lo);self.hi=F(lo if hi is None else hi);assert self.lo<=self.hi
    @staticmethod
    def co(x):return x if isinstance(x,I) else I(x)
    def __add__(self,other):
        b=self.co(other);return I(self.lo+b.lo,self.hi+b.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,other):return self+-self.co(other)
    def __rsub__(self,other):return self.co(other)+-self
    def __mul__(self,other):
        b=self.co(other);v=[a*c for a in (self.lo,self.hi) for c in (b.lo,b.hi)]
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,other):
        b=self.co(other);assert b.lo>0
        return self*I(1/b.hi,1/b.lo)
    def __rtruediv__(self,other):return self.co(other)/self
    def square(self):
        vals=[self.lo**2,self.hi**2]
        return I(0 if self.lo<=0<=self.hi else min(vals),max(vals))
def min_i(*xs):return I(min(x.lo for x in xs),min(x.hi for x in xs))
def max_i(*xs):return I(max(x.lo for x in xs),max(x.hi for x in xs))

SCALE=2**60
ROOT=(247054608130038637,823515360433462126,36028797018963968,
      307445734561825861,144115188075855872,480383960252852907)
def S_at(x,y):return (1+x.square()-2*x*(1+3*y)/(1+y))/(1-x.square())

def leaf_margin(box,sign,reason):
    x,y,h=[I(F(box[2*i],SCALE),F(box[2*i+1],SCALE)) for i in range(3)]
    if reason==10:return F(3,20)-(x-y).hi
    if reason==11:return (x+y).lo-F(3,4)
    if reason==12:return (h.square()+2*h).lo-1
    x2=x.square();y2=y.square()
    if reason==13:return ((1+3*y)/(1+y)).lo-((1+x2)/(1-x2)).hi
    Su=S_at(I(x.lo),I(y.lo)).hi
    if reason==14:return -Su
    den=(x-y)*(1+x*y);assert den.lo>0
    r=1-x;u=1-y;common=(1-x-y)/den
    X=r+y*(1-x2)*common;Y=2*x*y*common
    if reason==15:return X.lo-1
    if reason==16:return Y.lo-u.hi
    c=I((1-h.hi**2)/(1+h.hi**2),(1-h.lo**2)/(1+h.lo**2))
    s=I(2*h.lo/(1+h.lo**2),2*h.hi/(1+h.hi**2))
    if sign==1:
        M=max_i(s*u,c*X+s*Y);T=max_i(s*r,s*X-c*Y)
        if reason==17:return M.lo-1
        if reason==18:return (c*u+T).lo-1
        L=min_i(I(1),(1-M)/c,(1-T)/s)
        D=min_i(I(1),(1-M)/s,1/c-u)
    else:
        T=max_i(c*r,c*X-s*Y);M=max_i(c*u,s*X+c*Y)
        if reason==17:return (T+s*u).lo-1
        if reason==18:return M.lo-1
        L=min_i(I(1),(1-T)/c,(1-M)/s)
        D=min_i(I(1),1/s-u,(1-M)/c)
    if reason==19:return -L.hi
    if reason==20:return -D.hi
    assert L.hi>0
    # Exact-rational L.hi is no larger than the generator's rounded upper.
    # The A majorant is increasing in Z, so this gives a valid tighter bound.
    Z=I(L.hi/(2-L.hi));K=y2/(1-2*y2)
    b=y2.square()/((1-y2)*(1-3*y2))
    A1=Z+K
    if Z.hi<=F(1,10):A=A1
    else:A=min_i(A1,max_i(I(F(1,10))+K,Z+b*(1/Z-Z)))
    Au=min(F(1),A.hi);gl=2-Au-Su;vl=max(F(0),1-D.hi)
    assert gl>0
    if reason==21:return gl*gl-2
    if reason==22:return gl*vl-1
    if reason==23:return gl+vl*vl-2
    raise AssertionError(reason)

def verify(sign):
    start=time.time();folder=Path(__file__).with_name('round16_interval_certificate')
    path=folder/('C%d.tree'%sign)
    # This box encloses every exact rational endpoint of the claimed domain.
    for i,(a,b) in enumerate([(F(3,14),F(5,7)),(F(1,32),F(4,15)),(F(1,8),F(5,12))]):
        assert F(ROOT[2*i],SCALE)<=a<=b<=F(ROOT[2*i+1],SCALE)
    stack=[(ROOT,0)];counts={};nodes=0;depth_max=0;min_margin={}
    with path.open('rb') as inp:
        while stack:
            box,depth=stack.pop();raw=inp.read(1);assert raw,'missing tree node'
            code=raw[0];nodes+=1;depth_max=max(depth_max,depth)
            if code in (0,1,2):
                j=2*code;m=(box[j]+box[j+1])//2;assert box[j]<m<box[j+1]
                left=list(box);right=list(box);left[j+1]=m;right[j]=m
                stack.extend([(tuple(right),depth+1),(tuple(left),depth+1)])
            else:
                margin=leaf_margin(box,sign,code)
                assert margin>F(1,100000),{'sign':sign,'code':code,'box':box,'margin':str(margin)}
                counts[code]=counts.get(code,0)+1
                min_margin[code]=min(margin,min_margin.get(code,margin))
        assert inp.read(1)==b'','extra tree nodes'
    return {'C_sign':sign,'result':'INDEPENDENT_FRACTION_PASS','nodes':nodes,
        'leaves':sum(counts.values()),'max_depth':depth_max,'seconds':time.time()-start,
        'leaf_reasons':counts,'every_leaf_strict_margin_lower_bound':'1/100000',
        'strict_minimum_margins':{k:str(v) for k,v in min_margin.items()},
        'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

if __name__=='__main__':
    results=[verify(sign) for sign in [1,-1]]
    print(json.dumps([{k:v for k,v in r.items() if k!='strict_minimum_margins'}
        for r in results],indent=2))
    Path(__file__).with_name('round16_fraction_verification.json').write_text(
        json.dumps(results,indent=2),encoding='utf-8')
