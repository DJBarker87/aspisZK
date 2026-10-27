# Resume: release reachability under ruling (l)

Base c57a344726, prior failed source 138cf2cf7d; resumed from a964ac5c61.

| Edited file | Module gate in crates/aspis-r1-cost-probe/src/lib.rs | Release reachability |
|---|---|---|
| weights.rs | `pub mod weights;` (ungated) | Reachable. Restored byte-identical to c57a344726; no applied edit remains. |
| prover_powers.rs | `#[cfg(feature="prover")] mod prover_powers;` | Prover-only op254 copy. Only direct host calls in prover.rs and sim.rs redirected. Calls inside weights.rs remain original. |
| ct_pole.rs | `#[cfg(feature="ct-host-prover")] mod ct_pole;` | Host-only; explicit compile_error for ct-host-prover + program-build. |
| host_semantic.rs | `#[cfg(feature="prover")] mod host_semantic;` | Prover-only; op230 import redirect. |
| prover.rs | `#[cfg(feature="prover")] pub mod prover;` | Prover-only; op230 and op254 call redirects. |
| sim.rs | `#[cfg(feature="r1p-check")] pub mod sim;` | r1p-check enables prover; host-only redirects. |
| prover_helper_sum.rs | `#[cfg(feature="prover")] mod prover_helper_sum;` | Prover-only op230 copy. |
| lib.rs | Two added module declarations, each cfg(prover) | Both absent when prover disabled; no other lib.rs edit. |

programs/r1-cost-probe/Cargo.toml depends on aspis-r1-cost-probe with
optimized-terminal,program-build, plus crate default private-leaf-salts.
Its release CLI features pool-adapter,private-leaf-salts do not enable prover,
r1p-check or ct-host-prover. The devnet build changes only the public program IDs.
programs/aspis-pool, aspis-verifier and aspis-registry Cargo.toml have no dependency
on aspis-r1-cost-probe. Pool release features are
r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit.
No other shipped source changed. Static reachability is not the byte gate:
all three rebuilt ELF pins must still pass before extraction.
