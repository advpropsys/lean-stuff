# Two polynomial nonvanishing theorems

Define the integer polynomials

Q(q)=9q⁴−14q³−30q²−14q+1,

H(q)=13q⁶−30q⁵−78q⁴−94q³−78q²−30q+1.

For every integer q≥1, **Q(q)≠0 and H(q)≠0**. Both statements are proved in Lean. A separate conditional lemma states that if integer quantities satisfy ΔX−ΔY=8(t−s)P, P>0 and ΔX=ΔY=0, then s=t.

The graph-to-polynomial derivation, distances after vertex deletion and full graph-family exclusion are not formalized here. The Šoltés problem remains unresolved by these results. Application to graphs requires a separate proof identifying Q and H with the relevant changes in graph distances. No novelty claim is made for these arithmetic lemmas.
[Proof](https://github.com/advpropsys/lean-stuff/blob/main/soltes-polynomial-obstructions/proof.md) · [Lean sources](https://github.com/advpropsys/lean-stuff/tree/main/soltes-polynomial-obstructions/Research) · [Build and audit](https://github.com/advpropsys/lean-stuff/blob/main/soltes-polynomial-obstructions/REPRODUCE.md) · [Executable example](https://github.com/advpropsys/lean-stuff/blob/main/soltes-polynomial-obstructions/example.py)

## Related problem and sources

**Šoltés' problem.** For a connected graph G, let W(G) be the sum of graph distances over unordered vertex pairs. Find all graphs for which G−v is connected and W(G−v)=W(G) for every vertex v. The cycle C₁₁ satisfies this condition; the associated uniqueness conjecture asks whether it is the only such graph.

Ľubomír Šoltés, [*Transmission in graphs: A bound and vertex removing*](https://dml.cz/handle/10338.dmlcz/132387), Mathematica Slovaca 41(1) (1991), 11–16, **unnumbered problem on page 16** ([PDF](https://dml.cz/bitstream/handle/10338.dmlcz/132387/MathSlov_41-1991-1_2.pdf#page=7)). The original problem asks for a classification; it does not state uniqueness as a theorem.

Stijn Cambie, [*Towards the essence of Šoltés' problem*](https://arxiv.org/html/2406.03451v1), arXiv:2406.03451v1 (2024), **Definition 2 and Example 7**, supplies the arc-graph construction and a generalized-hexagon example relevant to these polynomial obstructions. The Lean results here are arithmetic lemmas; they neither prove nor disprove the general Šoltés problem.

## Citation

Konstantin Korolev (whitecircle).

```bibtex
@misc{korolev2026soltespolynomialobstructions,
  author = {Korolev, Konstantin},
  title = {Two polynomial nonvanishing theorems},
  year = {2026},
  note = {Affiliation: whitecircle},
  url = {https://github.com/advpropsys/lean-stuff/tree/main/soltes-polynomial-obstructions}
}
```
