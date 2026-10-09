# Source scope and verification

This repository contains the 129-module Lean library `KlebersConjecture`: 14 modules of
`KlebersConjecture/Partitions/` (Young diagrams), 7 modules of `KlebersConjecture/SetPartitions/`
(set partitions), 88 modules of `KlebersConjecture/SymmetricFunctions/` (symmetric functions) and
20 modules of `KlebersConjecture/Paper/` (the paper). The modules of the three general libraries
never import `KlebersConjecture/Paper/`; `KlebersConjecture/Partitions/` and
`KlebersConjecture/SetPartitions/` import no other local library. All local imports are included,
and every module is in the import closure of `KlebersConjecture.Paper.Audit`. Mathlib (`b2bf051`)
and Tau Ceti (`48fe7a5`) are pinned public Lake dependencies and are not included.

## Source preparation

The sources are those of the development tree, unchanged. `LOCAL_MODULES.json` records, for every
module, the path and hash in this release. `LIBRARY_MANIFEST.json` (in the repository root)
records the version, folders and file hashes of the three general libraries.

## Verification records

- `BUILD_CHECK.json`: the full build of this snapshot with `build.py`, in which every local module
  was compiled; the whole-environment axiom audit (the axioms reachable from all declarations of the
  `KlebersConjecture` modules); and the Batteries linters over all of them.
- `ENDPOINT_AUDIT.txt`: the output of `KlebersConjecture/Paper/Audit.lean`.
- `DEPENDENCIES.json`: the pinned Lake packages.
- `LOCAL_MODULES.json`: the module inventory.

## Changes since 1.0.0

Version 2.0.0 changes only the folder layout. The Lean library is now `KlebersConjecture`, and
every module moved as follows; declaration names, namespaces, statements and proofs are unchanged.

| 1.0.0 | 2.0.0 |
| --- | --- |
| `Schubert.Partitions.*` | `KlebersConjecture.Partitions.*` |
| `Schubert.SetPartitions.*` | `KlebersConjecture.SetPartitions.*` |
| `Schubert.SymmetricFunctions.*` | `KlebersConjecture.SymmetricFunctions.*` |
| `Schubert.ComplementaryProducts.*` | `KlebersConjecture.Paper.*` |
