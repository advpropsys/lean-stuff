# Graph examples and reproducible figures

The actual counterexample has **15,211,807,199,220,036,387,538,871,517,957 vertices**.
Its proof uses exact finite counting and bounds. We do not enumerate that graph
or compute its complete coefficient sequence.

![Certified coefficient valley](../figures/canonical_certified_valley.svg)

## The actual counterexample

`graph_example.py` specifies the graph through vertex labels and an exact
adjacency predicate. Its default parameters are the parameters of the closed
Lean theorem `Research.DominationCounterexample.canonical_connected_counterexample`:

```
q = 2147483647
b = q² + q + 1
w = 256
t = 5b
m = b(6q + 9)
L = wm
n = t + L
```

`Control('L', p, a)` has `0 ≤ p < b` and `a = 0, 1`.
`Control('R', p, a)` has `0 ≤ p < b` and `a = 0, 1, 2`.
The point labels enumerate `(1,a,b′)`, then `(0,1,a)`, then `(0,0,1)`.
The auxiliary graph joins the three controls in each right cell and joins
all six left/right control pairs whenever their point vectors have dot product
zero modulo `q`. A `Clone(u,v,c)` exists for each auxiliary edge `u < v` and
`0 ≤ c < w`. All controls form a clique in the final graph. Each clone is
adjacent exactly to its two endpoint controls.

This provides executable examples even for the huge graph:

```python
from graph_example import ProjectiveDominationGraph, Control, Clone

g = ProjectiveDominationGraph()
u = Control('L', 0, 0)            # point (1,0,0)
v = Control('R', g.q*g.q, 0)      # point (0,1,0)
x = Clone(u, v, 0)
assert g.valid_vertex(x)
assert g.adjacent(x, u) and g.adjacent(x, v)
assert not g.adjacent(x, Control('L', 0, 1))
```

The Python adjacency implementation is an illustration of the mathematical
definition, not a formally verified extraction of Lean code. Calling
`materialize()` on the canonical graph raises an error before enumeration.

`canonical_parameters.json` records exact integers and the bounds used in the
figure. With `K = t + L/2`, the size bands are
`J_A = [K − 1.09b, K − 0.91b]` and
`J_C = [K − 0.81b, K − 0.70b]`. Each contains more than one third of all
dominating sets. Outside both, the total probability is less than `2⁻¹⁸⁹`.
For the explicit integer `j = K − floor(43b/50)`, this bounds `d_j/D(G,1)`.
Finite pigeonhole yields some `i ∈ J_A` and `k ∈ J_C` with normalized
coefficients greater than `2⁻¹⁰⁶`. Thus `i < j < k`, and both outside
coefficients exceed the middle coefficient.

**The plot displays these certified inequalities.** The horizontal spans show
where the two existential coefficients can lie; they do not assert the same
bound for every coefficient in those bands. No exact coefficient curve or
exact location of the two larger coefficients is claimed. The middle index
is plotted in the centered coordinate `(j−K)/b`, approximately `−0.86`.
The script transcribes the proof bounds; it does not rerun Lean or independently
establish the full inequalities.

## Small examples for inspection

- `q2_graph.json`: the same projective construction with `q=2`, `w=1`,
  **182 vertices and 889 edges**. Labels and the complete edge list are saved.
  This is an example of the definition; it is **not certified to be a
  counterexample**, and its domination polynomial is not computed here.
- `toy_coefficients.json`: one left two-vertex cell and one right triangle,
  joined completely in the auxiliary graph, with `w=1`. The final graph has
  **14 vertices**. Its exact domination polynomial is computed in two ways:
  by the omitted-control formula and by independent enumeration of all
  `2¹⁴ = 16,384` vertex subsets. The results agree. This toy is **unimodal**,
  so it is **not a counterexample**.

![Exact toy coefficients](../figures/toy_exact_coefficients.svg)

For the exact toy computation, the formula is

```
D(G,x) = sum over omitted control sets P of
         x^(t − |P| + w e_F(P)) (1+x)^(w(m − e_F(P))).
```

The auxiliary graph has no isolated vertices. This makes the formula valid
also when every control is omitted: the forced clones then dominate all
controls. The counting script caps the number of enumerated controls at 22.

## Reproduce

Run from this `examples` directory with Python 3.10 or newer:

```sh
python3 graph_example.py
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt
.venv/bin/python make_plots.py
```

The first command uses only the standard library. It checks canonical adjacency
queries and refusal to materialize the huge graph, checks the small graph's
edge count, adjacency, symmetry and absence of loops, and compares the toy's
two exact counting methods. It regenerates the three JSON files. The plotting
command writes both SVG and PNG versions into `../figures/`.

The figures were generated and visually inspected with Matplotlib 3.10.9.
SVG preserves editable text; PNG is included for convenient sharing.
