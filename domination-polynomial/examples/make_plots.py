#!/usr/bin/env python3
"""Reproduce figures from saved exact integers and certified proof bounds."""
import json
from fractions import Fraction
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator

HERE = Path(__file__).resolve().parent
OUT = HERE.parent/'figures'
OUT.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans', 'font.size':11,
    'axes.spines.top':False,'axes.spines.right':False,
    'axes.labelcolor':'#252525','text.color':'#252525',
    'svg.fonttype':'none','svg.hashsalt':'domination-examples-v1','savefig.facecolor':'white'})
BLUE, ORANGE, RED = '#246487', '#b56825', '#9b3434'
data = json.loads((HERE/'canonical_parameters.json').read_text())
bands = [tuple(float(Fraction(v)) for v in band) for band in data['bands']]
jx = float(Fraction(data['middle_index']-data['K'], data['b']))
assert bands[0][1] < jx < bands[1][0]

fig, (ax, bx) = plt.subplots(2,1,figsize=(10,7.5),sharex=True,
    gridspec_kw={'height_ratios':[1,1.55]})
fig.subplots_adjust(left=.12,right=.97,top=.86,bottom=.15,hspace=.35)
fig.suptitle('A certified valley in domination counts',x=.12,ha='left',y=.97,
             fontsize=19,fontweight='bold')
fig.text(.12,.92,r'Canonical graph: $q=2^{31}-1$, $w=256$, $n\approx1.52\times10^{31}$',fontsize=12)
for a, (lo,hi), color, label in zip([ax,ax],bands,[BLUE,ORANGE],['$J_A$','$J_C$']):
    a.axvspan(lo,hi,color=color,alpha=.12,lw=0)
    a.hlines(1/3,lo,hi,color=color,lw=3)
    a.annotate('',xy=((lo+hi)/2,.465),xytext=((lo+hi)/2,1/3),
               arrowprops={'arrowstyle':'->','color':color,'lw':2})
    a.text((lo+hi)/2,.52,label+' total probability $>1/3$',ha='center',color=color,fontsize=11)
ax.text(jx,.12,'Outside both bands:\ntotal probability $<2^{-189}$',ha='center',fontsize=10)
ax.set_ylim(0,.66)
ax.set_yticks([0,1/3],['0','1/3'])
ax.set_ylabel('Band mass bound')
ax.set_title('Uniformly sample a dominating set; record its size.',loc='left',fontsize=11,pad=12)
for (lo,hi), color, label in zip(bands,[BLUE,ORANGE],[r'some $i\in J_A$',r'some $k\in J_C$']):
    bx.axvspan(lo,hi,color=color,alpha=.08,lw=0)
    bx.hlines(-106,lo,hi,color=color,lw=3)
    bx.annotate('',xy=((lo+hi)/2,-94),xytext=((lo+hi)/2,-106),
                arrowprops={'arrowstyle':'->','color':color,'lw':2})
    bx.text((lo+hi)/2,-86,label+'\n$p>2^{-106}$',ha='center',color=color,fontsize=11)
bx.plot([jx],[-189],marker='v',color=RED,ms=9)
bx.annotate('',xy=(jx,-202),xytext=(jx,-189),arrowprops={'arrowstyle':'->','color':RED,'lw':2})
bx.text(jx+.013,-183,'Explicit middle index $j$\n$p_j<2^{-189}$',ha='left',color=RED,fontsize=11)
bx.set_ylim(-210,-68)
bx.set_yticks([-200,-189,-150,-106,-80])
bx.grid(axis='y',color='#dddddd',lw=.6)
bx.set_xlim(-1.13,-.66)
bx.set_xticks([-1.09,-.91,-.86,-.81,-.70])
bx.set_xlabel(r'Centered size $(s-K)/b$, where $K=5b+L/2$')
bx.set_ylabel(r'Bound on $\log_2 p_s$'+'\n'+r'$p_s=d_s/D(G,1)$')
bx.set_title('Two coefficients exceed the middle coefficient; their exact positions are not computed.',
             loc='left',fontsize=11,pad=10)
fig.text(.12,.04,'Inequality certificate, not an exact coefficient curve. Arrows indicate strict bounds.\n'
         'Horizontal segments mark possible locations of the two existential coefficients.',fontsize=10,color='#555555')
for ext in ('svg','png'):
    fig.savefig(OUT/f'canonical_certified_valley.{ext}',dpi=180,metadata={'Date':None} if ext=='svg' else {})
plt.close(fig)

toy=json.loads((HERE/'toy_coefficients.json').read_text())
y=toy['coefficients']; x=range(len(y))
fig, ax=plt.subplots(figsize=(9,4.8))
fig.subplots_adjust(left=.11,right=.97,top=.79,bottom=.22)
fig.suptitle('A small, inspectable example of the gadget',x=.11,ha='left',y=.97,fontsize=18,fontweight='bold')
fig.text(.11,.87,'14 vertices: 5 clique controls and 9 degree-two clones. This example is unimodal.',fontsize=11)
ax.bar(x,y,color=BLUE,width=.72)
ax.xaxis.set_major_locator(MaxNLocator(integer=True))
ax.set_xlabel('Dominating-set size $s$')
ax.set_ylabel('Exact count $d_s$')
ax.grid(axis='y',color='#dddddd',lw=.6)
ax.set_axisbelow(True)
fig.text(.11,.06,'Illustration only — not a counterexample. Counts agree between the exact gadget formula\n'
         'and independent enumeration of all 16,384 vertex subsets.',fontsize=10,color='#555555')
for ext in ('svg','png'):
    fig.savefig(OUT/f'toy_exact_coefficients.{ext}',dpi=180,metadata={'Date':None} if ext=='svg' else {})
plt.close(fig)
print('Wrote canonical bound plot and exact toy plot, each as SVG and PNG.')
