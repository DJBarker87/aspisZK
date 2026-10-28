from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
plan=json.loads((E/'NBW_REPLAY_PLAN.json').read_text())
rows=[]
for item in plan:
 p=E/item['attempt']/'receipt.json'
 if not p.exists():continue
 rc=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()
 status='PASS' if rc['exit_status']==0 else 'TIMEOUT' if 'timed out' in log.lower() else 'FAIL'
 rows.append(dict(item,status=status,exit=rc['exit_status'],wall_seconds=rc['wall_seconds'],rss_kib=rc['peak_rss_kib']))
(E/'NBW_REPLAYS.json').write_text(json.dumps(rows,indent=2)+'\n')
header='| Predecessor | Replay | Status | Native cut |\n|---|---|---|---|\n'
(E/'NBW_REPLAYS.md').write_text('# Exact NBO replay status\n\n'+header+''.join(f"| {r['predecessor']} | {r['attempt']} | {r['status']} | `{r['harness'].split('::')[-1]}` |\n" for r in rows)+'\nPASS restores only that inherited local property/domain under exact KMX configuration; it does not close its stubbed callees. TIMEOUT supplies no credit or counterexample. Prior unchanged timeout shapes were not replayed. NBB add/fold steps use K046/K047 with exact prefix rename and KMX attributes; their Lean value/trace results are imported unchanged.\n')
assert len(rows)==32,('replay stage incomplete',len(rows))
assert len(list(E.glob('NBW_K*/receipt.json')))==50
summary=json.loads((E/'NBW_SUMMARY.json').read_text())
passed=[r['attempt'] for r in rows if r['status']=='PASS'];timeouts=[r['attempt'] for r in rows if r['status']=='TIMEOUT']
with (E/'NBW_query_BRIDGE.md').open('a') as f:
 f.write('\n## Terminal native and symbolic results\n\n')
 f.write(f"All32 retained compliant NBO local passes were replayed: {len(passed)} PASS, {len(timeouts)} TIMEOUT. Exact rows and inherited domains: NBW_REPLAYS.md/JSON. Six expected-copy controls pass and their six matched false-value controls fail. K001 is an excluded scratch compilation error. Every actual Kani invocation has a fresh frozen resolved graph match, offline execution, and unchanged before/after frozen lock hash. Exact target, source revision/hashes, dependencies, wall/RSS/swap and limits are in NBW_ATTEMPTS.jsonl.\n\n")
 f.write('NBW_Audit (L012) co-imports all seven new proof modules and unchanged NBO/NBF/NBB closure. All18 public top theorems use standard axioms only or none. These establish symbolic window/frame and finish-value association, all-eight-coordinate comparison, exact primitive model entries, Horner domain/primitive transport, sign-pattern coefficient totality and exact26-term grouping. They do not establish frozen native four_dots/folds or entire-writer equality.\n\n')
 f.write('## Remaining exact obligations and stop disposition\n\n')
 f.write('Whole native composite remains **OPEN**, not CLOSED-CONDITIONAL. Extra native obligations remain beyond the permitted NBA_/NBE_/NBC_ producer bridges. NBO_WriterEntry.same_writer is reused only as its existing model-side theorem; no source-refinement gap is reclassified as cryptographic trust.\n\n')
 f.write('| Member | Remaining obligation and why a new native gate is needed |\n|---|---|\n')
 f.write('| Allocation/ownership/finish | Full same-allocation arbitrary-capacity view and exact source enumerator ordinal/continuation, plus window/frame composition. Existing model finish induction and new KMX value laws are proved; one-cell allocation checks do not supply the whole native ownership association. |\n')
 f.write('| Rejected prefixes and dictionary installation | Install the re-established local source fragments at every exact native call site, including query rejection and mutable state effects. A model Result equality does not itself identify a native execution. |\n')
 f.write('| four_dots/op20 | Native arbitrary-prestate base-prefix/tail iteration, emitted/checked arithmetic step association and actual byte decoder/callback order. The26-term partition/model arithmetic is not a native step proof. |\n')
 f.write('| circle/line/op17/op16 | Complete coefficient return/effect and three Horner-call association to the frozen bodies, on the already printed domains. Canonicality and argument-cut passes are insufficient. |\n')
 f.write('| Field/comparison/conversion dictionary | Finish source-to-cohort primitive bindings at the actual callers; inherited natural multiplication theorems are reused via LPh_STUBS.md, never proved in Kani. Native local gates are qualified by their receipts, not promoted to a global installation. |\n')
 f.write('| Producers/same writer | NBA_NBC.prepare/geometry/scanOpening, NBA_Opening, NBE_Batch and NBC_FieldOps remain exactly named lower dependencies. After internal native rows close, compose on the same writer; no independent successful outputs may be introduced. |\n\n')
 f.write('Budget:50/50 configured Kani slots (including excluded K001 compiler failure),12/120 Lean compiles. Kani exhaustion is not used to abandon a pending Lean proof: all seven new pure-model modules and the complete audit are green. Every remaining internal row above requires a native association/validation gate; external producer rows remain their owners\' named bridges. No unchanged timed-out/memory-killed job was rerun or cap raised.\n\n')
 f.write('## Freeze and reproducibility\n\n')
 f.write('No repository crates/programs/Cargo changes;498 local frozen files match. No three-ELF rebuild trigger. Historical pins are inherited, not freshly reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. Exact external scratch patches/source versions are retained; no binary/object/ELF is committed. NBW_FINAL_HOST.json records unchanged imported cache objects and actual Aeneas resolution. The lane cache is retained; own target/solver scratch removed. No other worktree, keys, push or merge.\n')
with (E/'NBW_HANDOFF.md').open('a') as f:
 f.write('\n## Terminal handoff\n\nOPEN. Consume NBW_query_BRIDGE.md, NBW_REPLAYS.md, LPh_STUBS.md, NBW_ATTEMPTS.jsonl, NBW_SUMMARY.json and NBW_L012/receipt.json. Pure-model and axioms audit complete; native obligations remain member-by-member in the bridge. Resume with smaller native windows for failed capacity/rejection/iteration shapes, then actual dots/fold/Horner effect/value association. Do not repeat any recorded timeout unchanged. Preserve the existing cache and exact KMX patch/negative controls.\n')
print(json.dumps(dict(replayed=len(rows),passed=len(passed),timeouts=timeouts,summary=summary)))
