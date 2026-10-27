from pathlib import Path
import json
P=Path(__file__).resolve().parent
x=json.loads((P/'Rc6_premises.json').read_text());v=json.loads((P/'Rc6_validation.json').read_text());r=json.loads((P/'Rc6_005'/'receipt.json').read_text())
pins=dict(default='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',devnet='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',Pool='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548')
(P/'Rc6_inherited_ELF_pins.json').write_text(json.dumps(dict(status='Inherited pins, not rebuilt; no shipped source/cfg(kani) change',pins=pins),indent=2)+'\n')
text=f'''# Rc6 handoff

S2 OPEN; 100-bit release target not yet established. Branch `codex/cx-recount6-20261026`. All stage commits local; no push or merge.

## Established claim

`AspisR1.Rc6_Top.deployed` composes Rc5 with PFin parser gates and P6C accepted-run refinement on exactly the same cuts, run, TX2 witness, saved checkpoint, heap and event history. It re-derives the parser result at the Rc5 dictionary and retains Rc5's stronger finish continuation. It does not call older tops to select a different execution.

Before/after full statements: `Rc6_before-statement.lean.txt`, `Rc6_after-statement.lean.txt`. Their explicit input binder text is identical. Nested before: `P2Prime → FirstEntryVerifierConeJoin → ∃ parsed, facts ∧ sites ∧ Rc5_Cont.Outcome`. Nested after drops FirstEntry and adds a derived parser packet and P6 safe/full facts on the original existential witnesses. The decoder, prover, runtime, game, failure events, extraction guarantee, budget range and numerical conclusions are unchanged.

Dictionary equalities: `Rc6_Install.parser_base`, `p6_base`, `reconstruct`. Reverse transport: `Rc6_Statements.reverse` proves the entire original top conclusion; `Rc6_Forget.forget` preserves the precise existential witnesses. `Rc6_Equivalent.same_domain` shows no additional vacuity under retained extraction/oracle hypotheses.

## Mechanical recount

Fresh 92 focused kernel inventories, reviewed atomic-family correspondence and shared witness/guard/dictionary deduplication: `Rc6_premises.json`, `Rc6_field_catalog.json`, `Rc6_recount.py`. Existing ledger bytes verified intact before appending the new **Recount on Rc6_Top** section; `Rc6_ledger_append_check.json` records exact prefix/append hashes.

Actual antecedents: **83T+33P → 83T+32P** (eleven approved game clauses counted); implementation-only subtotal explicitly excludes those clauses: **83T+22P → 83T+21P**. Deployment only: **6T+13P → 6T+8P**. Aliases: **0T+2P unchanged**. Deduplicated total: **89T+46P → 89T+40P**; all retained audit rows **89T+48P → 89T+42P**. C=0 throughout. No trust/input law added.

Removed L099 (actual P), L195–L199 (mathematical deployment P). The four parser gates L129–L132 and seven SessionAPrepare leaves N108–N114 were already absent on Rc5; zero duplicate credit. Exact row diff and all class/owner totals are in the JSON and appended ledger. Remaining P coverage: {json.dumps(x['remaining_P_by_running_job'],sort_keys=True)}. `Rc6_REMAINING.md` tags every row; F3X_ L157, SCC_ L159, SAG_ finish, BEf_ L166, JFx_ fixture, others UNCOVERED. Concurrent job results are not imported.

## Non-vacuity and limitations

`Rc6_Nonvacuity.accepted_input` retains the same conditional accepted input with physical 1880-byte public bytes and stored proof, and excludes an always-rejecting driver under P2Prime. `same_domain` proves relative result-domain equivalence. Existing Rc5 runtime/dictionary fixtures are re-inspected by kernel inventory, not promoted to a joint fixture of all retained top inputs. JFx_ remains responsible for that joint instantiation. No conclusion is hidden in a new assumption.

P6 uses accepted-run refinement of actually issued ordered source logs and a defined ideal extension; it asserts no totality of unissued native syscall evaluations. `P6C_CarrierGap.independent` is retained evidence that mathematical P6 laws do not remove L166's actual SDK child/native/global effect association. No closure credit for global rejected-query-prefix transport, raw frozen3 join/runtime binding, remaining finish laws or source lowering.

## Validation and resource receipts

Budget fully used: **100/100 Lean** (8 proof modules, 92 fresh inventories), **0/10 Kani**. All 100 exit 0; no timeout, memory kill, swap, unchanged compile rerun, cap increase or reservation retry. One scope at a time: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; Lean -j1 -M7000 -DElab.async=false. No package replay. Scope receipts, exact commands, target/revision/source and dependency hashes, exits, wall/RSS/swap, stdout and full axioms: `Rc6_001`–`Rc6_100` and `Rc6_ATTEMPTS.jsonl`.

Top attempt Rc6_005: exit {r['exit_status']}, wall {r['wall_seconds']:.9f}s, peak RSS {r['peak_rss_kib']} KiB, swap {r['swaps']}, revision `{r['source_revision']}` with dirty source tree and exact source SHA `{r['source_hashes']['Rc6_Top.lean']}`. `#print axioms deployed`: [propext, Classical.choice, Quot.sound]. Every new theorem is separately printed and standard-only. Total focused compiler wall time {v['wall_seconds']:.3f}s; maximum attempt RSS {v['peak_rss_kib']} KiB. `Rc6_validation.json` records scope/source/axiom/path checks.

The read-only selected closure pins 1,726 modules, compares 1,201 repository sources, and retains 178 object-only inherited cache boundaries. Two known Op5T comment-only variants are recorded by exact diffs; no substantive source mismatch. Reused coherent SInt2/PFin objects and unchanged launcher; no build/monitor infrastructure repair. This is focused cache composition, not a fresh frozen-release dependency replay.

No shipped file, cfg(kani) harness, session A worktree/candidate, other worker prefix, wallet/key, toolchain or ELF changed. ELF rebuild trigger did not fire; `Rc6_inherited_ELF_pins.json` records the inherited default/devnet/Pool pins, not newly reproduced binaries.

## Remaining blockers and next deliverable

No owner decision pending. Import and compose the named covering-job closures on this same dictionary, retain the source/runtime trust boundary, and produce the full joint non-vacuity fixture. L186 source-to-frozen-ELF lowering remains. **L187 coherent frozen dependency replay** and **L188 final release-wide axioms/trust audit** remain release gates. Rc6 standard-axiom compilation closes neither gate. Budget exhausted: no further Lean/Kani run is authorized in this job.
'''
(P/'Rc6_HANDOFF.md').write_text(text)
