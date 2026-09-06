# Sharp log-concavity of alternating Motzkin roots

Define the Motzkin numbers by M₀=M₁=1 and
(n+3)Mₙ₊₁=(2n+3)Mₙ+3nMₙ₋₁ for every integer n≥1.
For n≥0, let Tₙ = Mₙ − Mₙ₋₁ + ⋯ + (−1)ⁿM₀. For n≥1, let rₙ = Tₙ^(1/n), the nonnegative real n-th root.
Then **rₙ₋₁ rₙ₊₁ < rₙ² for every n ≥ 6**, with the strict reverse at n = 5. Thus the starting index 5 is sharp.

This implies [Zhao's Conjecture 1, Integers 26 (2026), A55](https://math.colgate.edu/~integers/aa55/aa55.pdf), which asks for the weaker non-strict conclusion starting at index 9. The final Lean theorem uses the actual alternating sum, via `T_eq_alternating_sum`; its only hypothesis is the index bound.

The proof uses ratio bounds to derive root inequalities, a method also developed by [Hou–Li](https://arxiv.org/abs/2310.19234). The theorem establishes the exact starting index for strict log-concavity of this root sequence.
[Proof](https://github.com/advpropsys/lean-stuff/blob/main/motzkin-root-log-concavity/proof.md) · [Lean sources](https://github.com/advpropsys/lean-stuff/tree/main/motzkin-root-log-concavity/Research) · [Build and audit](https://github.com/advpropsys/lean-stuff/blob/main/motzkin-root-log-concavity/REPRODUCE.md) · [Executable example](https://github.com/advpropsys/lean-stuff/blob/main/motzkin-root-log-concavity/example.py)

![Root sequence and the sharp log-concavity threshold](https://raw.githubusercontent.com/advpropsys/lean-stuff/main/motzkin-root-log-concavity/example-plot.png)

The plot is numerical; each of the 56 displayed margin signs is checked by exact integer powers before rendering. The all-index statement is proved in Lean. [Exact sequence values and plotted data](https://github.com/advpropsys/lean-stuff/blob/main/motzkin-root-log-concavity/plot-data.csv) · [SVG](https://github.com/advpropsys/lean-stuff/blob/main/motzkin-root-log-concavity/example-plot.svg) · [PDF](https://github.com/advpropsys/lean-stuff/blob/main/motzkin-root-log-concavity/example-plot.pdf).

The figure uses Inter throughout and is available as a 600-dpi PNG and vector
SVG/PDF. To regenerate: keep the full repository checkout, install
[requirements-plot.txt](https://github.com/advpropsys/lean-stuff/blob/main/motzkin-root-log-concavity/requirements-plot.txt), and run `python3 plot.py`. The script uses
[the shared style](https://github.com/advpropsys/lean-stuff/blob/main/plot_style.py) and [bundled fonts](https://github.com/advpropsys/lean-stuff/blob/main/assets/fonts/inter/README.md);
no system font installation is required.

## Conjecture and source

**Zhao's log-concavity conjecture for roots of alternating Motzkin sums.** Feng-Zhen Zhao, [*The log-balancedness of the sequence for the alternating sums of Motzkin numbers*](https://math.colgate.edu/~integers/aa55/aa55.pdf), Integers 26 (2026), A55, **Section 3, Conjecture 1, page 8**. The conjecture states that the sequence (Tₙ^(1/n))ₙ≥₉ is log-concave. The Lean theorem proves strict log-concavity with the sharp starting index 5.
