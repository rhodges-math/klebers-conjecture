# Third-party material

This repository contains no third-party source files. All Lean sources under
`KlebersConjecture/` were written for this formalization.

## Downloaded dependencies

These packages are downloaded by Lake at the revisions pinned in `lakefile.toml` and
`lake-manifest.json`. They are not included in this repository and keep their own
licenses.

- Tau Ceti: [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti), commit
  `48fe7a5f9ba49e3b1c11a72f54f665abc128b36a` (Apache License 2.0).
- Mathlib: [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4), commit
  `b2bf051988bf69448bce88722cc09a05fea31662` (Apache License 2.0).
- Their own dependencies, pinned in `lake-manifest.json`: plausible, LeanSearchClient,
  importGraph, proofwidgets, aesop, Qq, batteries (Apache License 2.0) and Cli (MIT License).

## Project license

This repository is licensed under the Apache License 2.0; see [LICENSE](LICENSE) and
[NOTICE](NOTICE).
