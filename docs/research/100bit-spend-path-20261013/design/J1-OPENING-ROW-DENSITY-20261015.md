# Literal opening-row density module (2026-10-15)

`R1LiteralOpeningDensity` gives per-row independent-answer density bounds for literal transcript rows 27–30. The event readers are causal: `LiteralOpeningEvents.readGamma/readKappa/readFirst/readSecond` consume the already-completed prefix and the current row's message, and use only challenge entries from earlier rows to assemble opening context. `LiteralOpeningView.read` reads the completed 25-row semantic prefix and ordinary challenges 25 and 26. The current challenge is supplied separately to the row-specific event predicate, so the reader does not depend on that challenge.

The four density theorems are `row27_density`, `row28_density`, `row29_density`, and `row30_density`. They transfer the corresponding selected-opening event mass bounds through `LiteralOrdinaryDensity.density` for the literal sampler, under the matching prefix-round equation (`P.round = 27`, `28`, `29`, or `30`). Their exact rational budgets in `LiteralOpeningDensity.lean` are:

- Row 27 gamma: `336869026622539 * OpeningSamplerBound.gammaAtom`.
- Row 28 kappa: `600 * OpeningSamplerBound.atom`.
- Rows 29 and 30 folds: `9396508281846 * OpeningSamplerBound.atom` each.

`gamma_mean`, `kappa_mean`, `first_mean`, and `second_mean` are the corresponding fixed-message mass bounds. The target compiled at base revision `3c79ec30fa44f408c716bb345050c137e907fa67`, source SHA-256 `32ba2a1e313e8751d65183afea7d218341477a3758b3a6c0b8431d863f4d9250`, in 1.69 s (3,594,936 KiB peak RSS, zero swap), with eight standard axiom reports. Its package is `evidence/lean-literal-opening-density-20261015/`.

The local event definitions intentionally map a failed reader (`none`) to `False`, giving that branch zero indicator mass. A later terminal/acceptance argument must prove the relevant readers succeed on admitted executions; otherwise those executions are not represented by these local event inputs. This module does not establish that success fact, D3 or shared-oracle closure, terminal acceptance, or Rust source correspondence.

Source pins: `LiteralOpeningDensity.lean` 32ba2a1e313e8751d65183afea7d218341477a3758b3a6c0b8431d863f4d9250; `LiteralOpeningEvents.lean` 3be2bd2255d0723eeb03cfce47078d3b36d4ddba5592b0be8f5a1629eb22ece3; `LiteralOpeningView.lean` 93cfb9df271c07b97050a07e4628f3aa509c03a342d9fa53c05987a368ead557; `LiteralOpeningStages.lean` 78ef40830007bd0914a7670effd1471bae84abae0494a0179b9f6c72c72ef927; `SelectedOpeningEventMass.lean` 5c7ad8017e7dcca60c517d82cad5739cceea3491e7ab5e8b990f401042b46302; `LiteralOrdinaryDensity.lean` 7239850e2b77fd77091c3f2ec6b89d20f975b9755eb89dda90d594b784aa2ec0.
