#!/usr/bin/env python3
"""Draw two actual small graphs from the domination construction.

Every edge is drawn, including the complete graph on the controls. Neither
small graph is asserted to be a counterexample. The right-hand example is
the same 14-vertex graph used for the exact coefficient plot.
"""
import json
from itertools import combinations
from math import atan2, cos, pi, sin
from pathlib import Path
import sys

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.collections import LineCollection
from matplotlib.lines import Line2D

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1]))
from plot_style import configure_style, save_figure
from graph_example import ProjectiveDominationGraph

INK = '#24343b'
MUTED = '#637078'
LEFT = '#16776d'
RIGHT = '#bd603f'
CLONE = '#91a5ad'
PALE = '#d9e2e4'


def segment_collection(ax, edges, positions, **kwargs):
    ax.add_collection(LineCollection(
        [(positions[u], positions[v]) for u, v in edges], **kwargs))


def outside_positions(controls, auxiliary, radius):
    """Order clones by the angle of the midpoint of their two controls."""
    def angle(edge):
        u, v = edge
        return atan2(controls[u][1] + controls[v][1],
                     controls[u][0] + controls[v][0])
    order = sorted(range(len(auxiliary)), key=lambda i: (angle(auxiliary[i]), i))
    clones = [None] * len(auxiliary)
    for rank, index in enumerate(order):
        theta = -pi + 2*pi*(rank+.5)/len(order)
        clones[index] = (radius*cos(theta), radius*sin(theta))
    return controls + clones


def verify_graph(n, edges, controls):
    edge_set = {tuple(sorted(e)) for e in edges}
    assert len(edge_set) == len(edges)
    assert all(0 <= u < n and 0 <= v < n and u != v for u, v in edges)
    neighborhoods = [set() for _ in range(n)]
    for u, v in edges:
        neighborhoods[u].add(v)
        neighborhoods[v].add(u)
    assert all(len(neighborhoods[v]) == 2 for v in range(controls, n))
    assert all(v in neighborhoods[u] for u, v in combinations(range(controls), 2))
    return neighborhoods


def main():
    configure_style()
    graph = ProjectiveDominationGraph(q=2, w=1)
    vertices, edges = graph.materialize()
    saved = json.loads((HERE/'q2_graph.json').read_text())
    assert saved['vertices'] == [repr(v) for v in vertices]
    assert saved['edges'] == [list(e) for e in edges]
    assert len(vertices) == 182 and len(edges) == 889
    verify_graph(len(vertices), edges, graph.t)

    control_positions = []
    for vertex in vertices[:graph.t]:
        # Seven visible groups correspond to the seven projective points.
        offset = ((vertex.slot-.5)*.10 if vertex.side == 'L'
                  else (vertex.slot-1)*.095)
        theta = pi/2 + 2*pi*vertex.point/graph.b + offset
        radius = .75 if vertex.side == 'L' else 1.03
        control_positions.append((radius*cos(theta), radius*sin(theta)))
    index = {v: i for i, v in enumerate(vertices[:graph.t])}
    auxiliary = [(index[v.u], index[v.v]) for v in vertices[graph.t:]]
    positions = outside_positions(control_positions, auxiliary, 1.58)

    toy = json.loads((HERE/'toy_coefficients.json').read_text())
    t = toy['controls']
    toy_aux = toy['auxiliary_edges']
    assert t == 5 and toy['w'] == 1 and toy['vertices'] == 14
    toy_controls = [(.65*cos(pi/2+2*pi*i/t), .65*sin(pi/2+2*pi*i/t))
                    for i in range(t)]
    toy_positions = outside_positions(toy_controls, toy_aux, 1.35)
    toy_edges = list(combinations(range(t), 2)) + [
        (u, t+i) for i, edge in enumerate(toy_aux) for u in edge]
    neighborhoods = verify_graph(14, toy_edges, t)
    selected = {2, 3, 4}
    dominated = selected | set().union(*(neighborhoods[v] for v in selected))
    assert dominated == set(range(14))
    assert len(toy_edges) == 28

    fig = plt.figure(figsize=(13.2, 8.1))
    fig.subplots_adjust(left=.035, right=.975, bottom=.17, top=.77, wspace=.13)
    grid = fig.add_gridspec(1, 2, width_ratios=[1.25, 1])
    ax, bx = fig.add_subplot(grid[0]), fig.add_subplot(grid[1])
    fig.text(.055, .94, 'The graph behind the construction',
             fontsize=24, weight='bold', color=INK)
    fig.text(.055, .895, 'Small instances reveal the controls, clones and domination rule.',
             fontsize=12.5, color=MUTED)

    segment_collection(ax, edges[:595], positions,
                       colors=MUTED, linewidths=.34, alpha=.14, zorder=1)
    segment_collection(ax, edges[595:], positions,
                       colors=LEFT, linewidths=.53, alpha=.27, zorder=2)
    for ids, color, size in [(range(14), LEFT, 25), (range(14, 35), RIGHT, 25),
                             (range(35, 182), CLONE, 9)]:
        ax.scatter([positions[i][0] for i in ids], [positions[i][1] for i in ids],
                   s=size, color=color, edgecolors='white', linewidths=.35, zorder=3)
    ax.set_title('Projective example', loc='left', fontsize=16,
                 fontweight='bold', color=INK, pad=26)
    ax.text(0, 1.04, '182 vertices · 889 edges · q = 2, w = 1',
            transform=ax.transAxes, fontsize=11, color=MUTED)
    ax.legend(handles=[
        Line2D([], [], marker='o', linestyle='', color=LEFT, markersize=6,
               label='Left controls · 14'),
        Line2D([], [], marker='o', linestyle='', color=RIGHT, markersize=6,
               label='Right controls · 21'),
        Line2D([], [], marker='o', linestyle='', color=CLONE, markersize=5,
               label='Clones · 147')],
        loc='upper center', bbox_to_anchor=(.5, -.035), ncol=3,
        frameon=False, fontsize=9, handletextpad=.4, columnspacing=.8)

    segment_collection(bx, toy_edges, toy_positions,
                       colors=CLONE, linewidths=.85, alpha=.52, zorder=1)
    # Emphasize one actual edge from each unselected vertex to the selected set.
    witnesses = [(v, min(neighborhoods[v] & selected))
                 for v in range(14) if v not in selected]
    assert len(witnesses) == 11
    segment_collection(bx, witnesses, toy_positions,
                       colors=RIGHT, linewidths=1.35, alpha=.82, zorder=2)
    for ids, color, size in [(range(5, 14), PALE, 120), (range(2), LEFT, 190),
                             (sorted(selected), RIGHT, 250)]:
        bx.scatter([toy_positions[i][0] for i in ids],
                   [toy_positions[i][1] for i in ids], s=size, color=color,
                   edgecolors='white', linewidths=1.3, zorder=3)
    bx.scatter([toy_positions[i][0] for i in selected],
               [toy_positions[i][1] for i in selected],
               s=390, facecolors='none', edgecolors=RIGHT, linewidths=1, zorder=4)
    for i in range(t):
        bx.text(*toy_positions[i], str(i+1), ha='center', va='center',
                color='white', fontsize=8.5, weight='bold', zorder=5)
    bx.set_title('A dominating set you can inspect', loc='left', fontsize=16,
                 fontweight='bold', color=INK, pad=26)
    bx.text(0, 1.04, '14 vertices · 28 edges · 3 selected controls',
            transform=bx.transAxes, fontsize=11, color=MUTED)
    bx.text(.5, -.055, 'The three ringed vertices dominate the graph.\n'
            'Each other vertex has a highlighted edge to one of them.',
            ha='center', va='top', transform=bx.transAxes, fontsize=10, color=MUTED,
            linespacing=1.55)

    for axis in (ax, bx):
        axis.set_aspect('equal')
        axis.set_xlim(-1.74, 1.74)
        axis.set_ylim(-1.74, 1.74)
        axis.axis('off')
    fig.text(.055, .055, 'Every edge is shown. Controls form a clique; each clone has exactly two control neighbors.',
             fontsize=10.5, color=INK)
    fig.text(.055, .025, 'Construction illustrations only. The 14-vertex example is unimodal; neither panel is a certified counterexample.',
             fontsize=9.5, color=MUTED)
    output = HERE.parent/'figures'/'graph_example'
    save_figure(fig, output)
    plt.close(fig)
    print('Graph figure verified: 182 vertices / 889 edges match q2_graph.json; '
          '14 vertices / 28 edges, selected controls {3, 4, 5} dominate all vertices. '
          'Every edge is drawn. Exported SVG, PNG and PDF.')


if __name__ == '__main__':
    main()
