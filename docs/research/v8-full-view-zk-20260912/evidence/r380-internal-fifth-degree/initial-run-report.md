# R380 internal fifth-power polynomial degree lemmas

Status: scratch-only focused proof; no promotion or source-execution claim.

`R380InternalFifthDegree.lean` (SHA-256 `53c6cb1004dab30d35a02f5f0b9292bd71d054b27c6c377e770e384fb69b54b7`) imports `AspisV8R19.R378PairedFifthDegree` (SHA-256 `6cb2cfc099d5722cacc04fe604c19ee67f5e079bd3eab2f8bcf9fdf239f1e810`). It defines the requested `internalRound` as a linear layer over `if active i then (state i + constants i)^5 else state i`.

The two proved statements are `internalRound_degree`, with constant and state input degrees at most `d` and output degree at most `5*d`, and `two_internalRounds_degree`, with arbitrary two masks/matrices, degree-at-most-1 initial state and constants, and output degree at most 25. Both use `linear_degree`; the active branch applies addition and fifth-power bounds, while the inactive branch retains the input-state bound. These are generic polynomial facts only.

The pinned focused run was the sole attempt (no failures or retries): run ID `1790952289292760000`, receipt `.r21-scratch/aspis-focus-1790952289292760000.receipt.json`, raw log `.r21-scratch/aspis-focus-1790952289292760000.log`, source snapshot `.r21-scratch/aspis-focus-1790952289292760000.source.lean`. Exit 0; wall 0.96 s; GNU-time Lean-child max RSS 2,290,952 KiB; swap 0; flags `-j1 -M4500`; systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. The runner distinguishes GNU-time child RSS from systemd wrapper peak.

Both full `#print axioms` reports are `[propext, Classical.choice, Quot.sound]`. No Rust execution correspondence, selected-source identification, or release obligation is claimed.
