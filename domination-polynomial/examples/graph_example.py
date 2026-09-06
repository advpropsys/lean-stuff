#!/usr/bin/env python3
"""Succinct canonical graph and small inspectable examples (standard library only)."""
from dataclasses import dataclass
from itertools import combinations
from math import comb, isqrt
import json
from pathlib import Path

CANONICAL_Q = 2147483647
CANONICAL_W = 256

@dataclass(frozen=True, order=True)
class Control:
    side: str
    point: int
    slot: int

@dataclass(frozen=True)
class Clone:
    u: Control
    v: Control
    copy: int

class ProjectiveDominationGraph:
    """Implicit graph: labels and adjacency work without enumerating vertices.

    q must be prime. Labels of clones use lexicographically ordered endpoints.
    The default is the Lean-verified counterexample; small parameters illustrate
    its definition but are NOT asserted to be counterexamples.
    """
    def __init__(self, q=CANONICAL_Q, w=CANONICAL_W):
        if q < 2 or any(q % d == 0 for d in range(2, isqrt(q) + 1)):
            raise ValueError('q must be prime')
        if not isinstance(w, int) or w < 1:
            raise ValueError('w must be a positive integer')
        self.q, self.w = q, w
        self.b = q*q + q + 1
        self.t = 5*self.b
        self.m = self.b*(6*q + 9)
        self.L = w*self.m
        self.n = self.t + self.L

    def point(self, i):
        if not 0 <= i < self.b:
            raise ValueError('projective point index out of range')
        if i < self.q*self.q:
            return (1, i // self.q, i % self.q)
        if i < self.q*self.q + self.q:
            return (0, 1, i - self.q*self.q)
        return (0, 0, 1)

    def valid_control(self, u):
        return (isinstance(u, Control) and u.side in ('L', 'R')
                and 0 <= u.point < self.b
                and 0 <= u.slot < (2 if u.side == 'L' else 3))

    def auxiliary_adjacent(self, u, v):
        if not self.valid_control(u) or not self.valid_control(v) or u == v:
            return False
        if u.side == v.side:
            return u.side == 'R' and u.point == v.point
        return sum(a*b for a, b in zip(self.point(u.point), self.point(v.point))) % self.q == 0

    def valid_vertex(self, x):
        if isinstance(x, Control):
            return self.valid_control(x)
        return (isinstance(x, Clone) and self.valid_control(x.u)
                and self.valid_control(x.v) and x.u < x.v
                and self.auxiliary_adjacent(x.u, x.v)
                and 0 <= x.copy < self.w)

    def adjacent(self, x, y):
        if not self.valid_vertex(x) or not self.valid_vertex(y) or x == y:
            return False
        if isinstance(x, Control) and isinstance(y, Control):
            return True
        if isinstance(x, Clone) and isinstance(y, Control):
            return y in (x.u, x.v)
        if isinstance(y, Clone) and isinstance(x, Control):
            return x in (y.u, y.v)
        return False

    def materialize(self, limit=10000):
        """Return labels and integer-indexed edges, only for bounded examples."""
        if self.n > limit:
            raise ValueError(f'{self.n} vertices exceeds materialization limit {limit}; use adjacency queries')
        controls = [Control(s, p, a) for s in ('L', 'R')
                    for p in range(self.b) for a in range(2 if s == 'L' else 3)]
        aux = [(u,v) for u,v in combinations(controls, 2) if self.auxiliary_adjacent(u,v)]
        assert len(aux) == self.m
        clones = [Clone(u,v,c) for u,v in aux for c in range(self.w)]
        vertices = controls + clones
        lookup = {v:i for i,v in enumerate(controls)}
        edges = list(combinations(range(self.t),2))
        edges += [(lookup[u],self.t+i) for i,x in enumerate(clones) for u in (x.u,x.v)]
        assert len(vertices) == self.n
        return vertices, edges


def gadget_coefficients(t, aux_edges, w):
    """Exact domination polynomial, enumerating only the 2^t omitted controls.

    Auxiliary graph must have no isolated vertices; every positive w works.
    Sum_P x^(t-|P|+w e(P)) (1+x)^(w(m-e(P))).
    """
    if t > 22:
        raise ValueError('exact omitted-control enumeration capped at 22 controls')
    assert w >= 1 and {v for e in aux_edges for v in e} == set(range(t))
    L = w*len(aux_edges)
    out = [0]*(t+L+1)
    for mask in range(1 << t):
        e = sum(bool(mask >> u & 1) and bool(mask >> v & 1) for u,v in aux_edges)
        forced = w*e
        base = t-mask.bit_count()+forced
        for z in range(L-forced+1):
            out[base+z] += comb(L-forced,z)
    return out


def brute_domination_coefficients(t, aux_edges, w):
    """Independent exhaustive check of the tiny example on final graph vertices."""
    n = t+w*len(aux_edges)
    assert n <= 20
    neighborhoods = [(1 << t)-1 for _ in range(t)]
    for u,v in aux_edges:
        for _ in range(w):
            idx = len(neighborhoods)
            neighborhoods.append((1 << idx) | (1 << u) | (1 << v))
            neighborhoods[u] |= 1 << idx
            neighborhoods[v] |= 1 << idx
    counts = [0]*(n+1)
    for selected in range(1 << n):
        dominated, remaining = 0, selected
        while remaining:
            bit = remaining & -remaining
            dominated |= neighborhoods[bit.bit_length()-1]
            remaining ^= bit
        if dominated == (1 << n)-1:
            counts[selected.bit_count()] += 1
    return counts


def main():
    here = Path(__file__).resolve().parent
    g = ProjectiveDominationGraph()
    K = g.t + g.L//2
    j = K - (43*g.b)//50
    data = dict(q=g.q,w=g.w,b=g.b,controls=g.t,auxiliary_edges=g.m,clones=g.L,
                vertices=g.n,K=K,middle_index=j,
                formal_theorem='Research.DominationCounterexample.canonical_connected_counterexample',
                meaning='Certified inequalities, not computed exact coefficients',
                normalized_size_coordinate='(size-K)/b',
                bands=[['-109/100','-91/100'],['-81/100','-70/100']],
                each_band_mass_strict_lower_bound='1/3',
                outside_mass_strict_upper_bound='2^-189',
                middle_coefficient_probability_strict_upper_bound='2^-189',
                existential_coefficient_probability_in_each_band_strict_lower_bound='2^-106')
    assert g.n == 15211807199220036387538871517957
    try:
        g.materialize()
        raise AssertionError('canonical materialization must be refused')
    except ValueError:
        pass
    # Query genuine canonical vertices without expanding the graph.
    u, v = Control('L',0,0), Control('R',g.q*g.q,0)
    x = Clone(u,v,0)
    assert g.auxiliary_adjacent(u,v) and g.valid_vertex(x) and g.adjacent(x,u)
    assert not g.adjacent(x,Control('L',0,1))
    (here/'canonical_parameters.json').write_text(json.dumps(data,indent=2)+'\n')
    small = ProjectiveDominationGraph(q=2,w=1)
    vertices, edges = small.materialize()
    assert all(small.adjacent(vertices[u],vertices[v]) for u,v in edges)
    assert all(small.adjacent(u,v) == small.adjacent(v,u) for u in vertices for v in vertices)
    assert sum(small.adjacent(u,v) for u,v in combinations(vertices,2)) == len(edges)
    assert all(not small.adjacent(v,v) for v in vertices)
    (here/'q2_graph.json').write_text(json.dumps(dict(
        status='Illustration only; not a certified counterexample',q=2,w=1,
        vertices=[repr(v) for v in vertices],edges=edges),indent=2)+'\n')
    # One left I2 cell, one right K3 cell, joined completely: t=5,m=9,n=14.
    aux = [(2,3),(2,4),(3,4)] + [(u,v) for u in (0,1) for v in (2,3,4)]
    coefficients = gadget_coefficients(5,aux,1)
    assert coefficients == brute_domination_coefficients(5,aux,1)
    mode = max(range(len(coefficients)), key=coefficients.__getitem__)
    unimodal = (all(coefficients[i] <= coefficients[i+1] for i in range(mode))
                and all(coefficients[i] >= coefficients[i+1] for i in range(mode,len(coefficients)-1)))
    assert unimodal
    (here/'toy_coefficients.json').write_text(json.dumps(dict(
        status='Exact illustrative 14-vertex graph; unimodal, NOT a counterexample',
        controls=5,w=1,auxiliary_edges=aux,vertices=14,
        coefficients=coefficients,unimodal=unimodal,
        verified_by='Exact omitted-control formula AND independent full dominating-set enumeration'),indent=2)+'\n')
    print(f'Canonical adjacency queries passed; {g.n} vertices (implicit).')
    print(f'q=2,w=1 example: {len(vertices)} vertices, {len(edges)} edges.')
    print('14-vertex toy: exact formula equals independent enumeration; unimodal.')

if __name__ == '__main__':
    main()
