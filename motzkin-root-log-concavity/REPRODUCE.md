
## Reproduce

With elan and the pinned dependencies available, run from this folder:

```sh
lake build Research
lake env lean Audit.lean
python3 example.py
```

Lean 4.29.0; mathlib commit `8a178386ffc0f5fef0b77738bb5449d50efeea95`. The Python example uses only the standard library. The stated results are proved in Lean; [verification.log](https://github.com/advpropsys/lean-stuff/blob/main/motzkin-root-log-concavity/verification.log) records the repository build and axiom audit. No external peer review has been completed.
