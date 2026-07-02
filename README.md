# BooleanIsoperimetry

Lean 4 formalization of Harper's vertex-isoperimetric theorem for the
Boolean cube.

The main theorem says that among all subsets of the `n`-dimensional Boolean
cube with a fixed cardinality `k`, the initial segment in simplicial order has
the smallest closed Hamming-1 neighborhood.

```lean
theorem harper_theorem
    (n : Nat) (A : Finset (Cube n)) (k : Nat) (hk : A.card = k) :
    (neighborhood 1 (simplicialInitSeg n k)).card <=
      (neighborhood 1 A).card
```

The formalization follows the short proof of Harper's theorem by
P. Frankl and Z. Furedi:

- P. Frankl and Z. Furedi,
  "A short proof for a theorem of Harper about Hamming-spheres",
  Discrete Mathematics 34 (1981), 311-313.
  [doi:10.1016/0012-365X(81)90009-1](https://doi.org/10.1016/0012-365X(81)90009-1)
  / [ScienceDirect page](https://www.sciencedirect.com/science/article/pii/0012365X81900091).

An expository version that was also useful while organizing the proof is
[Harper's Theorem](https://cseweb.ucsd.edu/~ccalabro/essays/harper.pdf), which
presents the Frankl-Furedi proof in a more expanded form.

## Status

- Lean version: `leanprover/lean4:v4.31.0`.
- Mathlib version: pinned by `lake-manifest.json`.
- The project builds with `lake build`.
- The formal proof of `harper_theorem` is sorry-free.
- The active Lean source is intended to be warning-free and mathlib-style.

## Building

From the repository root:

```bash
lake exe cache get
lake build
```

For a focused check of the final theorem file:

```bash
lake env lean BooleanIsoperimetry/Harper.lean
```

## Mathematical Structure

The proof has three interacting layers.

1.  The Boolean cube layer defines cubes, Hamming distance, neighborhoods,
    simplicial order, initial segments, and the Harper boundary function `H`.

2.  The Macaulay/Kruskal-Katona layer proves the shadow and cascade estimates
    needed to control how boundary size changes across Hamming spheres.

3.  The Frankl-Furedi compression layer reduces an arbitrary family to a
    canonical compressed family without increasing its neighborhood, then
    connects that canonical form back to the scalar Harper recurrence.

The final file assembles these ingredients into the vertex-isoperimetric
statement above.

## File Guide

### `BooleanIsoperimetry.lean`

Top-level import file for the library.  Importing this file loads the public
formalization modules:

- cube and neighborhood definitions,
- cascade and Macaulay arithmetic,
- Kruskal-Katona shadow tools,
- compression infrastructure,
- the final Harper theorem.

### `BooleanIsoperimetry/Cube.lean`

Foundational API for the Boolean cube.

Main contents:

- `Cube n`, represented as `Finset (Fin n)`;
- Hamming distance `hDist`;
- closed neighborhoods `neighborhood`;
- Hamming balls and basic cardinality facts;
- simplicial/colex order on cube vertices;
- binary encodings and rank-style helper lemmas;
- simplicial initial segments `simplicialInitSeg`;
- coordinate-slice maps `embed0`, `embed1`, `slice0`, and `slice1`;
- the Harper boundary function
  `H n k = (neighborhood 1 (simplicialInitSeg n k)).card`;
- basic monotonicity, full-cube, and slice-recursion facts for `H`.

This is the file to read first: nearly all later files use its definitions.

### `BooleanIsoperimetry/Cascade.lean`

Binomial and Macaulay cascade infrastructure.

Main contents:

- binomial-prefix arithmetic;
- `IsBinomialCascade`;
- `CascadeSplit`, the split of a simplicial initial segment into lower and
  upper coordinate slices;
- existence, uniqueness, and bound lemmas for cascade splits;
- the connection between `CascadeSplit` and slices of
  `simplicialInitSeg`;
- recurrence lemmas for `H`, including the cascade form of the successor
  dimension;
- helper estimates for `HIncrement`.

This file is the bridge between the geometric Boolean-cube object and the
numeric cascade expressions used later.

### `BooleanIsoperimetry/Macaulay.lean`

Arithmetic of the increment profile of the Harper function.

Main contents:

- `HIncrement`, the discrete increment profile of `H`;
- sum formulas such as `H_eq_sum_HIncrement`;
- the explicit layer weight `macaulayShadowWeight`;
- formulas identifying `HIncrement` and interval counts with sums of these
  Macaulay weights;
- layer-window bounds;
- nested cascade and interleaving infrastructure;
- scalar boundary-cost estimates used by the final Harper argument.

This is the main numeric workspace for the Macaulay side of the proof.

### `BooleanIsoperimetry/KruskalKatona.lean`

Kruskal-Katona upper-shadow layer theorem.

Main contents:

- Hamming layers/spheres;
- initial segments inside a fixed layer;
- upper shadows of layer families;
- the numeric upper-shadow value `upperShadowVal`;
- theorems showing that initial layer segments minimize upper-shadow size.

The key results include `upperLayerShadow_min` and
`upperShadowVal_numeric_min`.  They connect the project-specific upper-shadow
language to the lower-shadow Kruskal-Katona tools available in mathlib.

### `BooleanIsoperimetry/LayerWindows.lean`

Layer-window accounting used to translate Kruskal-Katona shadow information
into the window inequalities required by the Harper recurrence.

Main contents:

- layer-window ranges;
- per-layer cost functions for pairs of initial segments;
- explicit window counts;
- lemmas comparing pair costs to Kruskal-Katona/Macaulay shadow quantities;
- wrappers that expose the shadow-minimization theorem in the form needed by
  the compression and Harper files.

This file is a technical bridge: it turns layer-wise set-family estimates into
the scalar windows used in the final recurrence.

### `BooleanIsoperimetry/SimplicialCompression.lean`

Coordinate-compression operations on families of cube vertices.

Main contents:

- coordinate up-compression and down-compression;
- predicates saying that a family is fixed by a compression;
- compression potentials used for termination/descent;
- lemmas showing that compression does not increase the closed
  Hamming-1 neighborhood;
- initial-slice-pair constructions and embedded-neighborhood cardinality
  calculations.

This file supplies the operational compression tools behind the Frankl-Furedi
route.

### `BooleanIsoperimetry/Compression.lean`

Frankl-Furedi paired-compression layer.

Main contents:

- embedded two-slice families;
- decomposition of neighborhoods across the two coordinate slices;
- pair shadow costs and canonical cascade pairs;
- PDF-style up/down block operations;
- family Hamming-distance tools;
- fully compressed families;
- terminalization/descent machinery;
- family-level reduction theorems.

Important theorems include:

- `exists_fullyCompressed_le`;
- `simplicialInitSeg_neighborhood_card_min`;
- `franklFuredi_pairedCompression_exchange`.

This is the file closest in spirit to the Frankl-Furedi proof: it proves that
one can pass from an arbitrary family to a canonical compressed family without
increasing the relevant neighborhood size.

### `BooleanIsoperimetry/Shadow.lean`

Upper-shadow and Macaulay exchange layer for Harper's theorem.

Main contents:

- upper-shadow definitions for layer sizes;
- closed forms for the Harper boundary in terms of shadows;
- positive Macaulay exchange inequalities;
- scalar split-minimization lemmas;
- the master family-level theorem `harper_vertex_iso`;
- bridges from shadow-sum statements to the final scalar inequalities.

This file is where the Kruskal-Katona and Macaulay estimates are assembled into
the main exchange/minimization statements.

### `BooleanIsoperimetry/SetFamilyShadow.lean`

A small compatibility layer between the project's shadow notation and the
Kruskal-Katona layer theorem.

Main contents:

- equality between the numeric `upperShadow` expression and the cardinality of
  the corresponding set-family upper shadow;
- `upperShadow_numeric_min`, a convenient numeric minimization theorem derived
  from `KruskalKatona.lean`.

This file keeps the set-family shadow theorem reusable without duplicating the
larger shadow development.

### `BooleanIsoperimetry/MacaulayMin.lean`

Downstream Macaulay minimization and compression-descent consequences.

Main contents:

- oriented Macaulay extremal steps;
- max-form wrappers for the two Harper recurrence cases;
- `macaulay_bc_min`, the scalar boundary-cost minimization theorem;
- `harper_macaulay_min`;
- `initialSlicePair_harper_bound`;
- `harper_compression_descent`.

This file packages the numeric and compression results into the form consumed
by the final theorem assembly.

### `BooleanIsoperimetry/Harper.lean`

Final theorem assembly.

Main contents:

- scalar boundary-cost definitions;
- interval and window counts for `gShift`;
- exact window-sum lemmas;
- induction and case-split lemmas for the Harper recurrence;
- `harper_bc_min`;
- `harper_core`;
- the final public theorem `harper_theorem`.

This is the endpoint of the formalization.  If you only want to inspect the
final statement and its immediate dependencies, start here and follow the
imports backward.

## Build Files

### `lakefile.toml`

Lake project configuration.  It defines the package, imports mathlib, enables
the standard mathlib linter set, and keeps `relaxedAutoImplicit` disabled.

### `lean-toolchain`

Pins the Lean toolchain:

```text
leanprover/lean4:v4.31.0
```

### `lake-manifest.json`

Lake dependency lockfile.  This records the exact dependency revisions used by
the formalization.

## Suggested Reading Order

For the code:

1. `Cube.lean`
2. `Cascade.lean`
3. `KruskalKatona.lean`
4. `Macaulay.lean`
5. `LayerWindows.lean`
6. `SimplicialCompression.lean`
7. `Compression.lean`
8. `Shadow.lean`
9. `SetFamilyShadow.lean`
10. `MacaulayMin.lean`
11. `Harper.lean`

For the mathematics:

1. Frankl-Furedi's short proof of Harper's theorem.
2. The expository Harper note linked above.
3. The Lean files, using `Harper.lean` as the map of how the components are
   finally assembled.

## Related Work

The formalization is about Harper's original vertex-isoperimetric theorem.  A
natural next direction is the stability theory for the same problem, for
example:

- Stability for vertex isoperimetry in the cube,
  [arXiv:1807.09618](https://arxiv.org/abs/1807.09618).

The current project deliberately builds several set-family and compression
notions in a way that should be useful for such future stability
formalizations.
