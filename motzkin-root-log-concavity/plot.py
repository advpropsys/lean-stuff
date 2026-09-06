"""Plot exact recurrence data; plotted roots/logs are floating-point illustrations.

Requires matplotlib (see requirements-plot.txt). Every shown margin sign is
checked independently by exact integer powers before plotting.
"""
from pathlib import Path
import csv
import math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parent
M = [1, 1]
for n in range(1, 60):
    numerator = (2*n+3)*M[n] + 3*n*M[n-1]
    assert numerator % (n+3) == 0
    M.append(numerator // (n+3))
T = [1]
for n in range(1, len(M)):
    T.append(M[n]-T[n-1])
rows = []
for n in range(4, 60):
    left = T[n]**(2*(n*n-1))
    right = T[n-1]**(n*(n+1))*T[n+1]**(n*(n-1))
    sign = (left > right)-(left < right)
    if n == 5:
        assert sign == -1
    if n >= 6:
        assert sign == 1
    root = math.exp(math.log(T[n])/n)
    margin = 2*math.log(T[n])/n-math.log(T[n-1])/(n-1)-math.log(T[n+1])/(n+1)
    assert (margin > 0)-(margin < 0) == sign
    rows.append((n, T[n], root, margin, sign))
with (OUT/'plot-data.csv').open('w', newline='') as handle:
    writer = csv.writer(handle, lineterminator="\n")
    writer.writerow(['n','T_n_exact','root_approx','log_concavity_margin_approx','exact_margin_sign'])
    writer.writerows(rows)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig, axes = plt.subplots(1, 2, figsize=(11, 4.3))
fig.subplots_adjust(bottom=.26, top=.78, wspace=.30)
fig.suptitle('Alternating Motzkin roots: a sharp threshold', fontsize=17, x=.08, ha='left', y=.96)
ns = [r[0] for r in rows]
axes[0].plot(ns, [r[2] for r in rows], color='#146356', lw=2)
axes[0].set(title='The root sequence', xlabel='Index n', ylabel=r'$T_n^{1/n}$')
axes[1].plot(ns, [r[3] for r in rows], color='#146356', marker='.', markersize=5)
axes[1].axhline(0, color='#777777', lw=.8)
axes[1].set_yscale('symlog',linthresh=.0001)
axes[1].set(title='Log-concavity margin (symmetric log scale)', xlabel='Center n', ylabel=r'$\Delta_n = 2\log r_n - \log r_{n-1} - \log r_{n+1}$')
r5 = next(r for r in rows if r[0] == 5)
axes[1].scatter([5],[r5[3]],color='#b23735',s=45,zorder=5)
axes[1].annotate('Center 5 fails', xy=(5,r5[3]), xytext=(18,-.015),arrowprops={'arrowstyle':'->','color':'#b23735'},color='#b23735')
for ax in axes:
    ax.grid(axis='y', alpha=.18)
fig.text(.08,.10,'Lean proves every center n ≥ 6 is positive and center 5 is negative.\nThe plot shows n = 4…59; heights are numerical, with every displayed sign checked by exact integer powers.',fontsize=10,color='#444444')
fig.savefig(OUT/'example-plot.svg',bbox_inches='tight')
fig.savefig(OUT/'example-plot.png',dpi=180,bbox_inches='tight')
print('Wrote plot-data.csv, example-plot.svg and example-plot.png; 56 exact sign checks passed.')
