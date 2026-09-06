# Proof

Integrality gives b_A+b_B+b_C≥(2−|S∩A|)+(1−|S∩B|)+(2−|S∩C|)=5−|S|. The integer budget sum is at most 3/2, hence at most 1. Therefore |S|≥4.

The unique independent set of size at least four in P₇ is {1,3,5,7}. Indeed, four nonconsecutive positions in seven places must have gaps exactly two and start at one. This set misses A and requires b_A≥2, contradicting b_A≤1.

The weaker formulation is feasible: S={1,4,7} takes one vertex from each part, and real budgets (1/2,0,1/2) work. Thus the integer-budget condition is essential.

The Lean graph is indexed 0 through 6, one less than the labels in this explanation. It proves connectivity, the actual partition, equivalence to mathlib independence, and the contradiction for all integer budgets.
