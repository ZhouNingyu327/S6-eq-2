"""Integer outward intervals for the full continuous three-parameter domain.

Every operation rounds outwards to a dyadic interval, using integer arithmetic.
The pre-order certificate records a binary subdivision of an enclosing box;
each leaf must be excluded by a necessary geometric inequality. This is not
sampling placements or covering a finite point set.
"""
from pathlib import Path
import json, hashlib, time, argparse

PREC=60; SCALE=1<<PREC
def R(a,b=1): return (a*SCALE//b,-((-a*SCALE)//b))
def P(a): return (a,a)
def add(a,b): return a[0]+b[0],a[1]+b[1]
def sub(a,b): return a[0]-b[1],a[1]-b[0]
def neg(a): return -a[1],-a[0]
def mul(a,b):
    v=(a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1])
    return min(v)//SCALE,-((-max(v))//SCALE)
def div(a,b):
    assert b[0]>0
    lo=min(a[0]*SCALE//b[0],a[0]*SCALE//b[1])
    hi=max(-((-a[1]*SCALE)//b[0]),-((-a[1]*SCALE)//b[1]))
    return lo,hi
def sq(a):
    lo=0 if a[0]<=0<=a[1] else min(a[0]*a[0],a[1]*a[1])
    hi=max(a[0]*a[0],a[1]*a[1])
    return lo//SCALE,-((-hi)//SCALE)
def mn(*args):return min(a[0] for a in args),min(a[1] for a in args)
def mx(*args):return max(a[0] for a in args),max(a[1] for a in args)
ONE=R(1); TWO=R(2); ZERO=R(0); THREE=R(3); TEN=R(1,10)
ROOT=(R(3,14)[0],R(5,7)[1],R(1,32)[0],R(4,15)[1],R(1,8)[0],R(5,12)[1])
REASONS={
    10:'x-y >= 3/20',11:'x+y <= 3/4',12:'h^2+2h <= 1',
    13:'long-leg cosine bound',14:'short bottom leg nonnegative',
    15:'Q.x <= 1',16:'Q.y <= u',17:'C first support width <= 1',
    18:'C second support width <= 1',19:'C left endpoint length positive',
    20:'C downward endpoint length nonnegative',21:'F chord squared <= 2',
    22:'F triangle twice-area <= 1',23:'F three-point bound g+v^2 <= 2',
}

def scalar_S(x,y):
    return div(sub(add(ONE,sq(x)),mul(mul(TWO,x),div(add(ONE,mul(THREE,y)),add(ONE,y)))),sub(ONE,sq(x)))

def reject(box,sign):
    x,y,h=(box[0:2],box[2:4],box[4:6])
    if sub(x,y)[1]<R(3,20)[0]:return 10
    if add(x,y)[0]>R(3,4)[1]:return 11
    if add(sq(h),mul(TWO,h))[0]>SCALE:return 12
    x2=sq(x);y2=sq(y)
    Lmin=div(add(ONE,mul(THREE,y)),add(ONE,y))
    Mcos=div(add(ONE,x2),sub(ONE,x2))
    if Lmin[0]>Mcos[1]:return 13
    # S is decreasing in both x and y throughout this enclosing box.
    Sl=scalar_S(P(x[1]),P(y[1]))[0]
    Su=scalar_S(P(x[0]),P(y[0]))[1]
    S=(Sl,Su)
    if Su<0:return 14
    den=mul(sub(x,y),add(ONE,mul(x,y)))
    if den[0]<=0:return 0
    r=sub(ONE,x);u=sub(ONE,y)
    common=div(sub(sub(ONE,x),y),den)
    Y=mul(mul(mul(TWO,x),y),common)
    X=add(r,mul(mul(y,sub(ONE,x2)),common))
    if X[0]>SCALE:return 15
    if Y[0]>u[1]:return 16
    # cos is decreasing, sin increasing for h in [1/8,5/12].
    def c_at(t):return div(sub(ONE,sq(P(t))),add(ONE,sq(P(t))))
    def s_at(t):return div(mul(TWO,P(t)),add(ONE,sq(P(t))))
    c=(c_at(h[1])[0],c_at(h[0])[1])
    s=(s_at(h[0])[0],s_at(h[1])[1])
    cu=mul(c,u);su=mul(s,u)
    if sign==1:
        M=mx(su,add(mul(c,X),mul(s,Y)))
        T=mx(mul(s,r),sub(mul(s,X),mul(c,Y)))
        if M[0]>SCALE:return 17
        if add(cu,T)[0]>SCALE:return 18
        L=mn(ONE,div(sub(ONE,M),c),div(sub(ONE,T),s))
        D=mn(ONE,div(sub(ONE,M),s),sub(div(ONE,c),u))
    else:
        T=mx(mul(c,r),sub(mul(c,X),mul(s,Y)))
        M=mx(cu,add(mul(s,X),mul(c,Y)))
        if add(T,su)[0]>SCALE:return 17
        if M[0]>SCALE:return 18
        L=mn(ONE,div(sub(ONE,T),c),div(sub(ONE,M),s))
        D=mn(ONE,sub(div(ONE,s),u),div(sub(ONE,M),c))
    if L[1]<=0:return 19
    if D[1]<0:return 20
    # The actual z is below L/(2-L). Taking only an outward upper endpoint
    # preserves all feasible placements, including all possible left shifts.
    Z=div(P(L[1]),sub(TWO,P(L[1])))
    Zu=Z[1]
    K=div(y2,sub(ONE,mul(TWO,y2)))
    b=div(sq(y2),mul(sub(ONE,y2),sub(ONE,mul(THREE,y2))))
    A1=add(P(Zu),K)
    if Zu<=TEN[0]:A=A1
    else:
        # b <= 256/36993 < 1/101, hence H(z)=z+b(1/z-z)
        # is increasing for z >= 1/10. For z <= 1/10, A <= 1/10+K.
        H=add(P(Zu),mul(b,sub(div(ONE,P(Zu)),P(Zu))))
        A=mn(A1,mx(add(TEN,K),H))
    Au=min(SCALE,A[1])
    gl=2*SCALE-Au-Su
    vl=max(0,SCALE-D[1])
    if gl>0 and gl*gl>2*SCALE*SCALE:return 21
    if gl>0 and gl*vl>SCALE*SCALE:return 22
    if gl>0 and gl*SCALE+vl*vl>2*SCALE*SCALE:return 23
    return 0

def children(box,axis):
    i=2*axis;m=(box[i]+box[i+1])//2
    assert box[i]<m<box[i+1]
    a=list(box);b=list(box);a[i+1]=m;b[i]=m
    return tuple(a),tuple(b)

def generate(sign,limit):
    start=time.time();stack=[ROOT];counts={};nodes=0
    root_width=[ROOT[2*i+1]-ROOT[2*i] for i in range(3)]
    axis_weights=[root_width[(i+1)%3]*root_width[(i+2)%3] for i in range(3)]
    folder=Path(__file__).with_name('round16_interval_certificate');folder.mkdir(exist_ok=True)
    path=folder/('C%d.tree'%sign)
    with path.open('wb') as out:
        while stack:
            box=stack.pop();nodes+=1
            reason=reject(box,sign)
            if reason:
                out.write(bytes([reason]));counts[reason]=counts.get(reason,0)+1
            else:
                axis=max(range(3),key=lambda j:(box[2*j+1]-box[2*j])*axis_weights[j])
                a,b=children(box,axis);out.write(bytes([axis]));stack.extend([b,a])
            if nodes%50000==0:
                print(json.dumps({'sign':sign,'nodes':nodes,'pending':len(stack),
                    'seconds':time.time()-start,'counts':counts}),flush=True)
            if nodes>=limit and stack:
                result={'sign':sign,'result':'INCOMPLETE','nodes':nodes,'pending':len(stack),
                    'seconds':time.time()-start,'counts':counts}
                print(json.dumps(result),flush=True);return result
    result={'sign':sign,'result':'FULL_DOMAIN_EXCLUDED','precision_bits':PREC,
        'root_dyadic_integers':ROOT,'nodes':nodes,'leaves':sum(counts.values()),
        'seconds':time.time()-start,'reasons':{REASONS[k]:v for k,v in counts.items()},
        'tree_file':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
    print(json.dumps(result),flush=True)
    return result

def verify(sign):
    path=Path(__file__).with_name('round16_interval_certificate')/('C%d.tree'%sign)
    stack=[ROOT];counts={};nodes=0
    with path.open('rb') as inp:
        while stack:
            box=stack.pop();raw=inp.read(1);assert raw,'incomplete subdivision'
            code=raw[0];nodes+=1
            if code<3:
                a,b=children(box,code);stack.extend([b,a])
            else:
                assert code in REASONS
                assert reject(box,sign)==code,(box,sign,code)
                counts[code]=counts.get(code,0)+1
        assert inp.read(1)==b'','unconsumed subdivision nodes'
    print(json.dumps({'sign':sign,'verification':'PASS','nodes':nodes,
        'leaves':sum(counts.values())}),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--sign',type=int,choices=[1,-1],required=True)
    ap.add_argument('--limit',type=int,default=1000000);ap.add_argument('--verify',action='store_true')
    args=ap.parse_args()
    if args.verify:verify(args.sign)
    else:
        result=generate(args.sign,args.limit)
        Path(__file__).with_name('round16_interval_C%d.json'%args.sign).write_text(
            json.dumps(result,indent=2),encoding='utf-8')
