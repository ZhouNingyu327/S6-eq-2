"""Exact rational example showing why axis endpoints alone miss the junction."""
from pathlib import Path
from fractions import Fraction as F
import itertools,json

def check():
    x,L,S,y,N=F(7,20),F(5,4),F(11,39),F(1,7),F(1)
    assert S==(1+x*x-2*x*L)/(1-x*x)
    l,r,u,d=F(1,2),F(13,20),F(6,7),F(31,100)
    a,b,v=F(2,3),F(28,39),F(69,100)
    pc,qc=F(299,349),F(180,349)
    assert pc*pc+qc*qc==1
    C=[(-l,0),(r,0),(0,u),(0,-d)]
    UU=[pc*X-qc*Y for X,Y in C];VV=[qc*X+pc*Y for X,Y in C]
    cwidths=[max(UU)-min(UU),max(VV)-min(VV)]
    assert all(w<1 for w in cwidths)
    FF=[(-a,0),(b,0),(0,v)]
    # At 45 degrees these numerators must be divided by sqrt(2).
    FU=[X+Y for X,Y in FF];FV=[-X+Y for X,Y in FF]
    fwidths=[max(FU)-min(FU),max(FV)-min(FV)]
    assert all(w*w<2 for w in fwidths)
    assert d+v==1
    assert a+b>1
    denom=(x-y)*(1+x*y)
    QY=2*x*y*(N-x-y)/denom
    QX=1-x+y*(1-x*x)*(N-x-y)/denom
    determinant=u*QX+l*(u-QY)
    assert determinant>1
    result={'classification':'counterexample to the sufficiency of a mu=1 axis-endpoint relaxation; NOT a target covering',
            'C_projection_widths':[str(t) for t in cwidths],
            'F_projection_width_numerators_over_sqrt2':[str(t) for t in fwidths],
            'bottom_chord':str(a+b),'Q':[str(QX),str(QY)],
            'twice_junction_triangle_area':str(determinant),
            'conclusion':'C and F axis endpoint requirements fit unit squares, but no unit C can also contain Q'}
    Path(__file__).with_name('round14_relaxation_example.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps(result),flush=True)
    return result

if __name__=='__main__':check()
