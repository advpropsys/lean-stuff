
## Reproduce

With elan and the pinned dependencies available, run from this folder:

```sh
lake build Research
lake env lean Audit.lean
python3 example.py
```

Lean 4.29.0; mathlib commit `8a178386ffc0f5fef0b77738bb5449d50efeea95`. The Python example uses only the standard library and illustrates the result; the universal proof is in Lean. `verification.log` records the publication-copy build and axiom audit. No historical-priority certification or external peer review is claimed.
