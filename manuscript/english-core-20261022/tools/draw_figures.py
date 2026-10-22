"""Generate English geometric figures; none is a six-tile counterexample."""
from pathlib import Path
import json, math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Rectangle, FancyArrowPatch
import numpy as np
OUT=Path(__file__).resolve().parents[1]/'figures'
OUT.mkdir(parents=True,exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Serif','font.size':10,'mathtext.fontset':'dejavuserif','pdf.fonttype':42})
blue='#215b82';orange='#b05b26';green='#40735a';gray='#71818b'
records=[]
def save(fig,name,desc):
    fig.savefig(OUT/(name+'.pdf'),bbox_inches='tight',pad_inches=.12)
    fig.savefig(OUT/(name+'.svg'),bbox_inches='tight',pad_inches=.12)
    plt.close(fig);records.append({'id':name,'description':desc,'type':'Exact schematic or labelled incidence diagram; not a feasible six-square covering.'})
def setup(ax,lim=1.35):
    ax.set_aspect('equal');ax.set_xlim(-lim,lim);ax.set_ylim(-lim,lim);ax.axis('off')
def target(ax,mu=1):
    ax.add_patch(Rectangle((-mu,-mu),2*mu,2*mu,fill=False,lw=1.6,color=gray))
    ax.plot([-mu,mu],[0,0],':',color=gray);ax.plot([0,0],[-mu,mu],':',color=gray)
def arrow(ax,p,q,color=blue):
    ax.add_patch(FancyArrowPatch(p,q,arrowstyle='->',mutation_scale=10,lw=1.1,color=color))
# 1. Coordinates and actual role names.
fig,ax=plt.subplots(figsize=(5.6,4.5));setup(ax);target(ax)
for i,(x,y) in enumerate([(-1,-1),(1,-1),(1,1),(-1,1)],1):
    ax.plot(x,y,'o',color=blue);ax.text(x*1.12,y*1.13,'$v_%d$'%i,ha='center',va='center')
for label,(x,y) in {'B':(0,-1),'R':(1,0),'T':(0,1),'L':(-1,0)}.items():
    ax.plot(x,y,'s',ms=4,color=orange)
    dx,dy=(.13*np.sign(x),0) if x else (0,.13*np.sign(y))
    ax.text(x+dx,y+dy,'$m_%s$'%label,ha='center',va='center')
ax.plot(0,0,'o',color=green);ax.text(.08,.07,'$O$')
ax.text(.48,.05,'$H_0$',color=gray);ax.text(.05,.50,'$V_0$',color=gray)
ax.text(0,-1.31,r'$T_\mu=[-\mu,\mu]^2,\qquad \mu>1$',ha='center')
save(fig,'01_target','Four corners, four outer midpoints, and two central segments.')
# 2. Cover-dominating push, showing only the first quadrant.
fig,axs=plt.subplots(1,2,figsize=(8,3.3))
c,s=.8,.6
def poly(alpha):
    return np.array([(c*p-s*q,s*p+c*q) for p,q in [(alpha,-.15),(alpha+1,-.15),(alpha+1,.85),(alpha,.85)]])
for ax,alpha,title in zip(axs,[-.2,0],['Original square','After the projection push']):
    ax.set_aspect('equal');ax.set_xlim(-.8,1.05);ax.set_ylim(-.38,1.5);ax.axis('off')
    ax.axhline(0,color=gray,lw=.7);ax.axvline(0,color=gray,lw=.7)
    ax.add_patch(Polygon(poly(alpha),closed=True,fc=blue,alpha=.17,ec=blue,lw=2))
    ax.plot(0,0,'o',color='black',ms=3)
    ax.text(.02,-.20,'Target corner');ax.set_title(title,fontsize=11)
    ax.text(.17,1.3,'$X,Y\\geq0$',fontsize=11)
    ax.text(-.7,1.05,('$[\\alpha,\\alpha+1]$' if alpha else '$[0,1]$'),fontsize=11)
save(fig,'02_normalization','Exact squares with c=4/5,s=3/5; containment is asserted only in the target quadrant.')
# 3. Two nonempty parallel chords.
fig,ax=plt.subplots(figsize=(5.5,4));ax.set_aspect('equal');ax.axis('off')
square=np.array([(0,0),(.8,.6),(.2,1.4),(-.6,.8)])
ax.add_patch(Polygon(square,closed=True,fc='#edf3f6',ec=blue,lw=1.8))
for x,low,high,label in [(-.5,2/3,.875,'I_1'),(.7,.525,11/15,'I_2')]:
    ax.plot([x,x],[-.13,1.55],':',color=gray)
    ax.plot([x,x],[low,high],color=orange,lw=4)
    ax.text(x+.04,(low+high)/2,'$%s$'%label,color=orange)
arrow(ax,(-.5,-.12),(.7,-.12),gray);arrow(ax,(.7,-.12),(-.5,-.12),gray)
ax.text(.10,-.24,'$d>1$',ha='center');ax.text(-.46,1.47,'Each line meets the same unit square',fontsize=10)
ax.set_xlim(-.8,1.02);ax.set_ylim(-.35,1.7)
save(fig,'03_parallel_chords','Exact unit square and vertical lines at distance 6/5; both chords have positive length.')
# 4. Near/far representatives, incidence only.
fig,axs=plt.subplots(1,2,figsize=(8,4))
for ax,kind,hosts,free in [(axs[0],'Near-end representative',{'R':2,'T':3,'L':4},1),(axs[1],'Far-end representative',{'R':2,'T':4,'L':1},3)]:
    setup(ax);target(ax)
    corners={1:(-1,-1),2:(1,-1),3:(1,1),4:(-1,1)}
    mids={'R':(1,0),'T':(0,1),'L':(-1,0)}
    for lab,owner in hosts.items():
        p=mids[lab];q=np.array(corners[owner])*.82
        ax.plot(*p,'s',ms=4,color=orange);arrow(ax,p,q)
    for i,p in corners.items():
        ax.text(p[0]*1.13,p[1]*1.13,('$W=V_%d$'%i if i==free else '$V_%d$'%i),ha='center',va='center',fontsize=10)
    ax.text(0,-.95,'$F$',ha='center',color=orange);ax.text(.04,.05,'$C\\ni O$',color=green)
    ax.set_title(kind,fontsize=11)
save(fig,'04_host_representatives','Arrows indicate chosen hosts; no tile shape or exclusive ownership is asserted.')
# 5. Gap endpoints.
fig,ax=plt.subplots(figsize=(7,1.9));ax.axis('off');ax.set_xlim(-1.2,1.2);ax.set_ylim(-.55,.65)
ax.plot([-1,1],[0,0],color=gray,lw=1)
ax.plot([-1,-.22],[0,0],color=blue,lw=5);ax.plot([.37,1],[0,0],color=green,lw=5)
ax.plot([-.22,.37],[0,0],color=orange,lw=3,ls='--')
ax.plot([-.22,.37],[0,0],'o',color=orange)
ax.text(-.64,.15,'Adjacent corner tile',ha='center')
ax.text(.72,.15,'Adjacent corner tile',ha='center')
ax.text(.075,-.23,'Open true gap',ha='center',color=orange)
ax.text(-.22,-.1,'$A$',ha='center',va='top');ax.text(.37,-.1,'$B$',ha='center',va='top')
ax.text(0,.48,'Closedness forces both endpoints into the same filling tile',ha='center',fontsize=10)
save(fig,'05_gap_endpoints','One-dimensional gap diagram; closure applies only when the entire open gap lies in one fixed closed tile.')
# 6. Candidate dependency DAG.
fig,ax=plt.subplots(figsize=(7.6,7.5));ax.axis('off');ax.set_xlim(0,10);ax.set_ylim(0,12)
boxes=[(5,11.2,'Arbitrary real six-square covering\\nActual roles and midpoint classification'),
       (5,9.6,'G5 exclusion\\nUnique centre tile and its interior'),
       (5,8.0,'G1, centre-G2, G4 and G3 exclusions\\nUniversal centre-no-mid statement'),
       (2.7,6.2,'Near-end G2\\nExclusion'),(7.3,6.2,'Inscribed-square argument\\nAxial root caps'),
       (5,4.5,'Far-end G2: gaps and horizontal states\\nFinal form with the same C and F'),
       (5,2.8,'Actual seams and four joining modes\\nUpper bridge / right bridge / double direct'),
       (5,1.1,'Angle and parameter-domain exclusions\\nProposed contradiction')]
for x,y,label in boxes:
    ax.text(x,y,label,ha='center',va='center',fontsize=9,bbox={'boxstyle':'round,pad=.5','fc':'#f1f5f7','ec':gray})
for p,q in [((5,10.75),(5,10.05)),((5,9.15),(5,8.45)),((4,7.55),(2.7,6.65)),((6,7.55),(7.3,6.65)),((2.7,5.75),(4,4.95)),((7.3,5.75),(6,4.95)),((5,4.05),(5,3.25)),((5,2.35),(5,1.55))]:arrow(ax,p,q,gray)
save(fig,'06_dependency_order','Arrows state the proposed dependency order; arithmetic checks do not certify these geometric implications.')
# 7. Actual inner unit squares; not a full covering.
fig,ax=plt.subplots(figsize=(5.5,4.7));setup(ax,1.34);target(ax,1.08)
c,s=12/13,5/13;centre=np.array([.03,.18])
origin=centre-np.array([c-s,s+c])/2
verts=np.array([origin,origin+[c,s],origin+[c-s,s+c],origin+[-s,c]])
ax.add_patch(Polygon(verts,closed=True,fc=blue,alpha=.16,ec=blue,lw=1.7))
ax.add_patch(Rectangle((-.5,-1.08),1,1,fc=orange,alpha=.16,ec=orange,lw=1.7))
ax.text(.35,.4,'$C$',fontsize=13,color=blue);ax.text(.32,-.93,'$F$',fontsize=13,color=orange)
# Compute the actual four intersections of C with the coordinate axes.
roots=[]
for axis in [0,1]:
    arr=[]
    for p,q in zip(verts,np.roll(verts,-1,axis=0)):
        if p[axis]*q[axis]<0:
            t=-p[axis]/(q[axis]-p[axis]);arr.append(p+t*(q-p))
    roots.extend(arr)
for p in roots:
    ax.plot(*p,'o',ms=3,color=blue)
    if abs(p[1])<1e-8:ax.text(p[0],.06,('$R_C$' if p[0]>0 else '$L_C$'),ha='center',fontsize=10)
    else:ax.text(.045,p[1],('$U_C$' if p[1]>0 else '$D_C$'),fontsize=10)
ax.plot(0,0,'o',ms=3,color='black');ax.text(-.10,.06,'$O$')
ax.text(0,-1.27,'Two illustrative unit tiles only; no six-tile covering is asserted.',ha='center',fontsize=8)
save(fig,'07_final_axes','Exact unit tiles illustrating axial endpoints, a bottom tile below H_0, and the same-tile convention.')
# 8. Four joining modes as intervals, never as a purported layout.
fig,axs=plt.subplots(2,2,figsize=(7.5,6))
modes=[('Double direct',True,True),('Upper bridge',True,False),('Right bridge',False,True),('Double bridge',False,False)]
for ax,(name,rd,ud) in zip(axs.flat,modes):
    ax.axis('off');ax.set_aspect('equal');ax.set_xlim(-.1,1.32);ax.set_ylim(-.25,1.25)
    ax.plot([0,1.15],[0,0],color=gray,lw=1);ax.plot([0,0],[0,1.15],color=gray,lw=1)
    rr=.92 if rd else .45;uu=.92 if ud else .45;tip=.75
    ax.plot([0,rr],[0,0],color=blue,lw=4);ax.plot([0,0],[0,uu],color=blue,lw=4)
    ax.plot([tip,1.15],[0,0],color=green,lw=3);ax.plot([0,0],[tip,1.15],color=green,lw=3)
    if not rd:ax.plot([rr,tip],[0,0],color=orange,lw=5)
    if not ud:ax.plot([0,0],[uu,tip],color=orange,lw=5)
    ax.plot(tip,0,'o',ms=3,color='black');ax.plot(0,tip,'o',ms=3,color='black')
    ax.text(tip,-.15,'$Q_R$',ha='center');ax.text(.06,tip,'$Q_U$')
    ax.text(.15,.2,'$C$',color=blue);ax.text(.87,1.04,'$W$',color=orange)
    ax.set_title(name,fontsize=11)
fig.text(.5,.02,'Blue: central axial interval. Green: anchored corner interval. Orange: a gap forced into W.',ha='center',fontsize=8)
save(fig,'08_joining_modes','The four membership predicates are exhaustive; interval endpoints are schematic, not a feasible covering.')
(OUT/'FIGURE_MANIFEST.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'figures':len(records),'directory':str(OUT)},indent=2))
