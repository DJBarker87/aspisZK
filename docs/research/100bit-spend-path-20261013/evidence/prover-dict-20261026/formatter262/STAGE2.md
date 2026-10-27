# Stage 2 — coefficient coordinate contract

## Checked Lean result

`R1Z.PDict_OwnedCorrect262.owned_value`: for every `T : Type`, Copy instance, extracted variant and 1024-element input array, the actual extracted owned reference returns `.ok (PDict_OwnedTarget262.target variant rows)`. All row/bounds/termination premises are discharged. The target is a symbolic tabulation of input coordinates selected by the actual extracted row call.

`R1Z.PDict_OwnedCorrect262.owned_read`: for every valid `i`, reading coordinate `i` after that owned execution has exactly the same complete `Result` as calling the actual extracted row selector and then reading the corresponding input coordinate. This includes the complete owned-reference Result; it does not assert native std::array::from_fn equality.

The proof follows symbolic cells → prefix extension → decreasing-remaining-count induction → generic bit bounds → concrete row totality → generic tabulation/read lemmas → complete reference equality. No 1024-step kernel reduction, increased limits, axiom, native_decide, backend or shipped-code change.

## Before / after

| Obligation | Before | After |
|---|---|---|
| Owned reference termination and every coordinate | open | proved for all T/Copy/variants/rows |
| Extracted row selector total and in range | open | proved using bit bounds and checked D-table certificates |
| Native Rust row versus reference row, all variants/positions<1024 | separate gate | Kani verified |
| Native full coefficient array versus scalar coordinate, all three types | open | OPEN; three timeouts, fixed-S1 solver failure |
| V262 native association / selected source counts | retained | retained; 175/255 selected, 80 open |
| V269/V270 Formatter axiom RELEASE BLOCKER | Stage 0 closed on candidate | unchanged; standard-only roots |
| Generic native Formatter adequacy / native type count | open /26 of28 | open /26 of28 |

## Focused Lean receipts

All rows use `lake env lean -M7000` on small new modules with existing read-only caches and no dependency build. RSS below is macOS bytes. Revision: `95287edb60` plus each exact retained source SHA in its receipt. Raw rejected source snapshots and sorryAx diagnostics remain historical rejection evidence. No failed module is accepted.

| Target | Attempt | Exit | Wall s | Peak RSS bytes | Swaps | #print axioms |
|---|---:|---:|---:|---:|---:|---|
| `PDict_OwnedCell262` | 26205 | 0 | 16.951 | 2213478400 | 0 | subset of propext, Classical.choice, Quot.sound |
| `PDict_OwnedPrefix262` | 26208 | 0 | 15.036 | 1691877376 | 0 | subset of propext, Classical.choice, Quot.sound |
| `PDict_OwnedLoop262` | 26210 | 0 | 19.143 | 2105688064 | 0 | subset of propext, Classical.choice, Quot.sound |
| `PDict_RowBits262` | 26212 | 0 | 20.336 | 1790001152 | 0 | subset of propext, Classical.choice, Quot.sound |
| `PDict_RowTotal262` | 26213 | 0 | 32.771 | 1748942848 | 0 | subset of propext, Classical.choice, Quot.sound |
| `PDict_Tabulate262` | 26216 | 0 | 10.026 | 2100609024 | 0 | subset of propext, Classical.choice, Quot.sound |
| `PDict_OwnedTarget262` | 26217 | 0 | 16.610 | 2190245888 | 0 | subset of propext, Classical.choice, Quot.sound |
| `PDict_CoordinatesEq262` | 26218 | 0 | 16.319 | 2160443392 | 0 | subset of propext, Classical.choice, Quot.sound |
| `PDict_ArrayRead262` | 26220 | 0 | 13.291 | 1862352896 | 0 | subset of propext, Classical.choice, Quot.sound |
| `PDict_OwnedCorrect262` | 26222 | 0 | 20.838 | 2015232000 | 0 | subset of propext, Classical.choice, Quot.sound |

All ten final new proof-module source hashes match their accepted snapshots; `local-summary.json`, `budget.json` and each `local/*-receipt.json` retain full commands, source revision, source/object hashes, cache dependencies and axiom output. `PDict_verify262.py` checks this without a replay.

Two concrete-use-site failures (J26214 `List.ofFn` simplification and J26219/J26221 array-read/congruence elaboration) reached default recursion depth. Replacements are permanent named generic `PDict_Tabulate262.get` and `PDict_ArrayRead262.read`, followed by constructor congruence. Caps were not raised. Other rejections are syntax/naming/proof adjustments, retained verbatim.

## Native receipts

Harnesses were named in `KANI-PLAN.md` before any charged invocation. All commands use optimized opt-level3, jobs4, unchanged host-run.py, 6G/8G/swap0/Tasks64 and the reused proof workspace/cache. Compilation happened on the first invocation; subsequent runs reuse it. Expected heavy work is the named array/bit-vector contract, not arithmetic elimination. A missing-Cargo PATH launch and one inner aggregate-reservation refusal precede Kani and are uncharged; their logs are retained. Both 3-minute contention waits were honored. No timeout was rerun unchanged.

| Harness | Label | Exit | Wall s | GNU RSS KiB | cgroup peak bytes | Swaps |
|---|---|---:|---:|---:|---:|---:|
| `row_index_native_reference` | pdict262-kani-001-path | 1 | 16.950 | 533956 | 796135424 | 0 |
| `row_index_native_reference` | pdict262-kani-001-retry1 | 0 | 0.951 | 153444 | 67674112 | 0 |
| `coordinate_m31_all` | pdict262-kani-002 | 124 | 120.168 | 15292 | 6599241728 | 0 |
| `coordinate_qm31_all` | pdict262-kani-003 | 124 | 120.004 | 15840 | 2329923584 | 0 |
| `coordinate_wide_all` | pdict262-kani-004 | 124 | 120.004 | 15640 | 4144336896 | 0 |
| `coordinate_m31_s1` | pdict262-kani-005 | 101 | 78.628 | 163124 | 3910795264 | 0 |

The single successful `row_index_native_reference` run reports 0/54 failed checks (one unreachable), with unwinding assertions enabled. It checks actual `Variant::row` against the retained safe reference and proves <1024 for every valid position and variant. It does not prove the array construction. All356 production input hashes from the native receipt match this worktree; see `production-source-binding.json`. Native raw revision label `783f890985+cfg-kani-PDict` is deliberately retained, not presented as the candidate revision: each input supplement pins this proof-only source, and the production equality check binds the reused workspace to the candidate. `#print axioms` is N/A for native verification.

GNU time under timeout undercounts descendants; cgroup peak is separate. Every cgroup swap peak is zero and no memory-pressure kill is recorded. No native type/source identity is inferred from a timeout.

## Host stop and remaining authorized allocation

The fixed-S1 M31 run exited101: `kissat: error: ...cnf:1: parse error: trailing zero missing`; Kani then panicked on unknown output variant `ERROR`. No mathematical verdict. Read-only `df` showed the host filesystem100% full, only19MiB available (`host-disk-full.txt`). Under local-lean.txt rule5, host launches stopped; no infrastructure repair or deletion was attempted. Further local proof work completed the owned-reference result.

Used23/100 Lean attempts (12 accepted including the two Stage0 audits;11 rejected/interrupted) and6/10 Kani invocations (one success, three timeouts, one compile rejection, one solver failure). Remaining77Lean/4Kani are **unspent, not exhausted**. Next unused env-J ID26223. Stage0 is complete via the explicitly allowed already-clean-closure exception; Stage1 required no dependency replacement. Host-only native work cannot continue while the filesystem is full.

Next concrete deliverable: after the lead restores host capacity, a successfully verified native monomorphic coefficient-array coordinate contract, starting with an unrun fixed-variant specialization from the retained plan, against `rows[reference_row::row(variant,position)]`. Preserve the native association until coverage/composition reaches all actual instantiated types and variants. The all-variant timeouts must not be rerun unchanged. No new OS-world law, dictionary entry, native type, headline hypothesis or authority was added or removed. Target not yet established.
