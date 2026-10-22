"""All-orientation FPS geometry by exact isolation of pair-projection events.

A subset is unit-box coverable at angle theta iff every pair has both absolute
projections <=1. Those truth values change only at quadratic roots in
t=tan(theta/2). Isolate each root in a dyadic bin exactly. In root-free gaps
use one exact rational frame of width 1; for root bins use an enclosing frame
box of width 1+2/M. This covers every orientation without a uniform fine grid.
"""
import argparse,hashlib,json,math,time
from pathlib import Path
import sys
import numpy as np
from numba import njit

from candidate_math import remove_dominated,members,solve_highs
from fastdfs2 import no_cover

def root_bins(a,b,c,M):
    if a==0:
        return [] if b==0 else [(-c*M)//b]
    disc=b*b-4*a*c
    if disc<0:return []
    # Exact floor of each algebraic root multiplied by M. With negative sqrt,
    # use ceil(sqrt(M^2*disc)); with positive sqrt use floor instead.
    sq=math.isqrt(M*M*disc)
    ceil=sq if sq*sq==M*M*disc else sq+1
    out=[]
    for sign in [-1,1]:
        h=-b;k=2*a
        if k<0:h=-h;k=-k;sign=-sign
        out.append((M*h+(sq if sign>0 else -ceil))//k)
    return out

def frames(P,q,M):
    bins={0,M-1}
    for i in range(len(P)):
        for j in range(i):
            dx=int(P[i,0]-P[j,0]);dy=int(P[i,1]-P[j,1])
            d2=dx*dx+dy*dy
            if not q*q<d2<=2*q*q:continue
            for x,y in [(dx,dy),(dy,-dx)]:
                for sign in [-1,1]:
                    for k in root_bins(-x-sign*q,2*y,x-sign*q,M):
                        if 0<=k<=M:bins.add(min(k,M-1))
    jobs=[];end=0
    for k in sorted(bins):
        if k>end:
            # t=(end+k)/(2M), strictly between root-containing bins.
            num=end+k;den=2*M
            g=math.gcd(num,den);num//=g;den//=g
            jobs.append((num,den,1,1))
        # t=k/M; angle error is <=2/M throughout this event bin.
        num=k;den=M;g=math.gcd(num,den);num//=g;den//=g
        jobs.append((num,den,M+2,M))
        end=k+1
    return jobs,len(bins)

@njit(cache=True)
def frame_sets(X,Y,A,B,width,W,out):
    U=A*X+B*Y;V=-B*X+A*Y
    ou=np.argsort(U);n=len(X);cnt=0;tmp=np.empty(n,np.int64)
    for ii in range(n):
        if ii and U[ou[ii-1]]==U[ou[ii]]:continue
        i=ou[ii];m=0
        for jj in range(ii,n):
            p=ou[jj]
            if U[p]-U[i]>width:break
            tmp[m]=p;m+=1
        vv=np.empty(m,np.int64)
        for t in range(m):vv[t]=V[tmp[t]]
        ov=np.argsort(vv);end=0;prev=-1
        for st in range(m):
            if end<st:end=st
            while end<m and vv[ov[end]]-vv[ov[st]]<=width:end+=1
            if end>prev:
                for w in range(W):out[cnt,w]=0
                for t in range(st,end):
                    p=tmp[ov[t]]
                    out[cnt,p>>6]|=np.uint64(1)<<np.uint64(p&63)
                cnt+=1;prev=end
    return cnt

def family(P,q,M):
    jobs,nbins=frames(P,q,M);n=len(P);W=(n+63)//64
    print('EVENT GEOMETRY',n,'points',nbins,'event bins',len(jobs),'frames',flush=True)
    buf=np.empty((n*n+1,W),np.uint64);sets=[]
    for num,den,bnum,bden in jobs:
        A=den*den-num*num;B=2*num*den;H=den*den+num*num
        width=(bnum*q*H)//bden
        assert (A+B)*int(P.max())<2**63 and width<2**63
        cnt=frame_sets(P[:,0],P[:,1],A,B,width,W,buf)
        sets.append(np.unique(buf[:cnt],axis=0))
    S=remove_dominated(np.unique(np.concatenate(sets),axis=0))
    return S,nbins,len(jobs)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('source');ap.add_argument('--out',required=True)
    ap.add_argument('--M',type=int,default=262144);ap.add_argument('--mip',action='store_true')
    ap.add_argument('--q',type=int,default=1000000)
    ap.add_argument('--dfs',action='store_true');args=ap.parse_args()
    d=json.loads(Path(args.source).read_text());oldq=int(d['q']);P=np.array(d['points_integer'],np.int64)
    q=args.q
    assert int(P.max())*q+oldq//2<2**63
    P=(P*q+oldq//2)//oldq
    assert P.min()>=0 and int(P.max())*d['a_den']<=d['a_num']*q
    t=time.time();S,nb,nf=family(P,q,args.M)
    np.save(args.out+'.npy',S)
    cert={k:d[k] for k in ['a','a_num','a_den','q','points_integer']}
    cert.update(q=q,points_integer=P.tolist())
    cert.update(method='critical_pair_events',M=args.M,npoints=len(P),nsets=len(S),event_bins=nb,frames=nf,
        family_sha256=hashlib.sha256(S.astype('<u8').tobytes()).hexdigest())
    print('CRITICAL FAMILY',len(S),'sets',round(time.time()-t,3),'seconds',flush=True)
    Path(args.out+'.json').write_text(json.dumps(cert,indent=2))
    if args.mip:
        r=solve_highs(members(S,len(P)),tl=90,threads=1)
        print('MIP (search only)',r[:3],flush=True)
        cert['mip']={'status':r[0],'objective':r[1],'dual_bound':r[2]}
        Path(args.out+'.json').write_text(json.dumps(cert,indent=2))
    if args.dfs:
        t=time.time();ok,st=no_cover(S,len(P),6)
        cert['exact_dfs']=dict(no_six_cover=bool(ok),nodes=int(st[0]),prunes=int(st[1]),seconds=round(time.time()-t,3))
        print('EXACT DFS',cert['exact_dfs'],flush=True)
        Path(args.out+'.json').write_text(json.dumps(cert,indent=2))

if __name__=='__main__':main()
