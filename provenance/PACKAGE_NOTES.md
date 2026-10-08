# Source scope and verification

This repository contains the 129-module Lean library `Schubert`: 14
modules of `Schubert/Partitions/` (Young diagrams), 7 modules of
`Schubert/SetPartitions/` (set partitions), 88 modules of
`Schubert/SymmetricFunctions/` (symmetric functions) and 20 modules of
`Schubert/ComplementaryProducts/` (the paper). The modules of the three general libraries never
import `Schubert/ComplementaryProducts/`; `Schubert/Partitions/` and `Schubert/SetPartitions/`
import no other local library. All local imports are included, and every module is in the import
closure of `Schubert.ComplementaryProducts.Audit`. Mathlib (`b2bf051`) and Tau Ceti (`48fe7a5`) are
pinned public Lake dependencies and are not included.

## Source preparation

The sources are those of the development tree, unchanged. `LOCAL_MODULES.json` records, for every
module, the path and hash in this release. `LIBRARY_MANIFEST.json` (in the repository root)
records the version, folders and file hashes of the three general libraries.

## Verification records

- `BUILD_CHECK.json`: the full build of this snapshot with `build.py`, in which every local module
  was compiled; the whole-environment axiom audit (the axioms reachable from all declarations of the
  `Schubert` modules); and the Batteries linters over all of them.
- `ENDPOINT_AUDIT.txt`: the output of `Schubert/ComplementaryProducts/Audit.lean`.
- `DEPENDENCIES.json`: the pinned Lake packages.
- `LOCAL_MODULES.json`: the module inventory.
