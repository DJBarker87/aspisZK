# R689 evidence bundle

This bundle retains the exact final R689 source, final source snapshot, compiler log and receipt, selected failed/intermediate attempts, and the exact compiled `.olean` artifact. `cache/PROVENANCE.json` records the original scratch cache path, canonical import cache path, SHA256 and the later R691 successful import receipt. The source copy in this bundle and canonical Lean source both hash to `17c36e529a3f42be8a898c4ce341f5a6479444c82fdf56df566119cecc07c3e4`.

The final focused compile is run ID `1791123656754152000`: exit 0, wall 1.08 s, peak Lean-child RSS 1,873,128 KiB, swap 0, Lean 4.32.0, `-j1 -M4500`, systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. Its complete `#print axioms` output is in `final.log`; source hash, revision, target and measurements are in `final.receipt.json`.

Retained attempts, chronological by run ID:

- `1791123235866632000`: broad `import Mathlib` raised Lean's configured excessive-memory exception (exit 134; RSS 5,867,460 KiB).
- `1791123260824082000`: attempted nonexistent `Mathlib.Tactic.Omega` object (exit 1).
- `1791123295220909000`: initial proof errors (including unavailable tactic and incomplete residue proof; exit 1).
- `1791123438655496000`: redundant tactic after the goal was already closed (exit 1).
- `1791123452795640000`: earlier, narrower theorem version compiled (exit 0); superseded by final source with explicit sum range/modulo lemmas.
- `1791123539899659000`, `1791123599405142000`, `1791123622406355000`: intermediate residue/modulo proof errors (exit 1 each).
- `1791123684410886000`: downstream R691 compile could not find R689 under its canonical module cache path (exit 1). Exact `.olean` was copied unchanged into the expected path; no R689 recompilation occurred.
- `1791124193496686000`: R691 imported the copied `.olean` and compiled successfully (exit 0). Its receipt and log are retained under `attempts/`.

All Lean attempts were bounded to `MemoryHigh=5G`, `MemoryMax=7G`, swap 0 and 128 tasks. The final R689 declarations report only Lean foundation axioms (`propext`, `Classical.choice`, `Quot.sound`); inspect the full output rather than relying on this summary. No root-generator/source correspondence is claimed here.
