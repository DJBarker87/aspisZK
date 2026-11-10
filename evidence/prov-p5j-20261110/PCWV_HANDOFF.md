# PCWV_ handoff (P5j, PAUSED by lead for PIN2)

Frozen 4bb3b3f. Toolkit copied from PCWR_ (renamed PCWV_, host workspace codex-pc-prov-p5j-20261110). Used: extraction scope PCWV_E001 (original Aeneas, ON, cargo --jobs 4, CARGO_BUILD_JOBS=4, exit 0, 27 s, peak RSS 0.59 GiB, swap 0). Lean scopes 0. Nothing running.

E001 roots: compact::check_values, BatchedWeights::value, push, update_residue_row, residue_limb_at, power_limb_at, with aspis_core includes (P, reduce_u64, from_le_bytes); emission in PCWV_E001_emitted/raw/PCWV_ev.
Findings: Option.Try branch/from_residual and Array.map and the IterMut into_iter are axioms in the fresh template; the gate defines the first two, so re-extract with includes. No equality proved; all 9 keys OPEN (PCWV_STATUS.json). No difference at a matching configuration found yet.
Stopped before: the PRVEq file and any Lean scope. Next steps in PCWV_REMAINING.json.

Target not yet established
