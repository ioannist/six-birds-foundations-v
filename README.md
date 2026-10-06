# Six Birds Foundations V

This repository is the public support surface for *Six Birds Foundations V:
Endogenous Closure — A Catalog of Structural Laws for Living, Cognitive, and
Social Systems*. It contains the modular manuscript, Lean 4 mechanization,
exact-arithmetic computational laboratory, formalization records, and vendored
Foundations dependencies used by the paper.

## Paper

- **Six Birds Foundations V: Endogenous Closure — A Catalog of Structural
  Laws for Living, Cognitive, and Social Systems**, Preprint v2.0,
  6 October 2026: `paper/main.pdf` with its supplement `paper/supplement.pdf`.
  DOI (v2.0): [10.5281/zenodo.23187543](https://doi.org/10.5281/zenodo.23187543);
  DOI (all versions): [10.5281/zenodo.22248766](https://doi.org/10.5281/zenodo.22248766);
  v1.0 (2 September 2026): [10.5281/zenodo.22248767](https://doi.org/10.5281/zenodo.22248767)

The paper develops an emergence calculus that moves the Six Birds closure
apparatus onto the carrier itself. An endogenous closure system carries its own instruments, ledgers, repair
generator, boundary records, and re-audit loop. Six definitions (D1–D6) and
sixteen structural entries (E1–E16) organize endogenous repair, bounded
self-audit, self-maintenance, priced exposure, alarm, probe acquisition, stack
rewrite, individuation, repair transport, reconsolidation, offline reclosure,
and adaptability. The entries are sorted by what is proved: five laws with a
Lean-checked instance (E1, E2, E3, E12, E13), general theorems, and
certificate specifications whose open obligation is stated. Version 2 corrects
version 1 in a revision appendix; in particular, the version-1 E2 capacity
measure and E1 forcing certificate admit no instance and are replaced.

Living, cognitive, and social systems are candidate realizations of the same
typed hypotheses, not metaphors for one another. The paper does not establish
a domain realization or claim a universal definition of life, consciousness,
death, welfare, or autonomous evolution.

## What This Repository Provides

- Modular LaTeX sources and the released PDF under `paper/`.
- Lean 4 representations of D1–D6 and E1–E16 under `lean/`, including the
  vendored Foundations III, Xi, and Holonomy support surfaces.
- An exact-arithmetic computational laboratory under `lab/`, with committed
  predictions and result records.
- Formalization manifests, gate panels, source inventories, examples, trust
  receipts, and traceability records under `formalization/`.
- The target-state theorem catalog in `THEOREMS.md`.
- Public verification and provenance notes under `docs/`.

Section 8 of the paper and the supplement's source concordance and formal
status record which parts of each printed statement are covered by Lean and
which are argued on paper or imported.

## Build and Verify

Build the manuscript and its supplement (also producing
`paper/build/main_flat.tex` and `paper/build/supplement_flat.tex`); the main
paper is built again so that its references into the supplement resolve:

```bash
cd paper
latexmk -pdf main.tex && latexmk -pdf supplement.tex && latexmk -g -pdf main.tex
```

Build the Lean project:

```bash
cd lean
lake build
```

Install and run the laboratory tests:

```bash
python3 -m venv .venv
.venv/bin/pip install -e "lab[dev]"
.venv/bin/pytest lab/tests
```

Validate the imported-foundations inventory:

```bash
python3 scripts/audit_foundations_dependencies.py
```

In a workspace containing the sibling Six Birds source repositories, require
source-text verification with:

```bash
python3 scripts/audit_foundations_dependencies.py --require-sources
```

Set `SIX_BIRDS_CORPUS_ROOT` or pass `--corpus-root` if those repositories do
not share this repository's parent directory. Continuous integration runs the
standalone inventory validation, Lean build, and laboratory tests.

## Repository Layout

- `paper/` — manuscript sources, bibliography, released PDF, and non-secret
  Zenodo submission configuration.
- `lean/` — the pinned Lean 4 project and vendored formal dependencies.
- `lab/` — computational laboratory package, tests, predictions, and results.
- `formalization/` — formalization manifests, examples, inventories, and
  verification records.
- `docs/` — public provenance and verification notes.
- `scripts/` — reproducibility and audit utilities.
- `THEOREMS.md` — the target-state theorem catalog.

## Notes

- The LaTeX build requires `latexmk` and the packages used by the manuscript.
- Lean is pinned by `lean/lean-toolchain` to `leanprover/lean4:v4.28.0`.
- The laboratory requires Python 3.10 or later.
- Vendored sources remain attributable to their upstream Six Birds projects.
- The manuscript's scope and nonclaims are authoritative where supporting
  records summarize them more briefly.
