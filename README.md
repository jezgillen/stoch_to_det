# stoch_to_det

Minimal Lean 4 checker artifact for the deterministic-partition bound.

## Public statements

The three headline declarations are collected in
`stoch_to_det/MainTheorems.lean`:

- `stoch_to_det.generalized_stoch_to_det_Cdagger1771_joint`
- `stoch_to_det.Cdagger1771_lt_1771`
- `stoch_to_det.LW_sum_1771_joint`

That file is the intended starting point for inspecting the theorem statements.

## Verification

Install `elan`, then run from this directory:

```sh
./verify.sh
```

The first run may download the pinned Lean toolchain and Mathlib dependencies.
The verifier:

1. rejects unfinished or disallowed source constructs;
2. builds the complete library;
3. checks transitively that the public declarations contain no `sorryAx`; and
4. validates their complete axiom dependencies against the expected set.

The expected axiom set for each public declaration is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

These are Lean's standard classical and quotient axioms. The development has
no project-defined axioms.

The two checker commands may also be run directly:

```sh
lake build --log-level=error stoch_to_det
lake env lean Verify.lean
```

## Reproducibility files

- `lean-toolchain` pins Lean.
- `lakefile.toml` declares the library and its Mathlib release.
- `lake-manifest.json` pins the complete transitive dependency graph.
- `stoch_to_det.lean` is the root module.
- `stoch_to_det/` contains the proof sources.
