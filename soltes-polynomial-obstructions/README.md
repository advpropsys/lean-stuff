# Two polynomial nonvanishing theorems

Define the integer polynomials

Q(q)=9q⁴−14q³−30q²−14q+1,

H(q)=13q⁶−30q⁵−78q⁴−94q³−78q²−30q+1.

For every integer q≥1, **Q(q)≠0 and H(q)≠0**. Both statements are proved in Lean. A separate conditional lemma states that if integer quantities satisfy ΔX−ΔY=8(t−s)P, P>0 and ΔX=ΔY=0, then s=t.

The graph-to-polynomial derivation, distances after vertex deletion and full graph-family exclusion are not formalized here. The Šoltés problem remains unresolved by these results. Application to graphs requires a separate proof identifying Q and H with the relevant changes in graph distances. No novelty claim is made for these arithmetic lemmas.
[Proof](https://github.com/advpropsys/lean-stuff/blob/main/soltes-polynomial-obstructions/proof.md) · [Lean sources](https://github.com/advpropsys/lean-stuff/tree/main/soltes-polynomial-obstructions/Research) · [Build and audit](https://github.com/advpropsys/lean-stuff/blob/main/soltes-polynomial-obstructions/REPRODUCE.md) · [Executable example](https://github.com/advpropsys/lean-stuff/blob/main/soltes-polynomial-obstructions/example.py)
