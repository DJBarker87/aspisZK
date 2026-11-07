from pathlib import Path
import json,hashlib
B=Path.cwd();review=json.loads((B/'NLV_REVIEW.json').read_text());ret=json.loads((B/'NLV_RETENTION.json').read_text());pins=json.loads((B/'NLV_PREDECESSOR_COMPARISON.json').read_text())
assert review['raw_axioms_standard']and ret['status']=='PASS'and all(not x['mismatches']for x in pins.values())
receipts=[json.loads(p.read_text())for p in sorted(B.glob('NLV_[LK][0-9][0-9][0-9]/receipt.json'))]
maxrss=max(int(r['peak_rss_kib'])for r in receipts);assert all(int(r['swaps'])==0 for r in receipts)
metrics=[{k:r[k]for k in ['attempt','kind','module','command','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}for r in receipts]
audit=dict(status='SUPPORT AUDIT COMPLETE; TX1:094 TARGET NOT ESTABLISHED',headline='AspisR1.RPx_Deployed.deployed',combined_import='NLV_L100/receipt.json',combined_audit_runs=1,NFX=dict(receipt='NLV_L106/receipt.json',exit=0,modules=review['modules'],dangling=0,conflicting_owners=0,import_mismatches=0,compatible_replicas=2420),raw_ax2=dict(groups=30,roots=review['required_roots'],own_roots=review['own_roots'],all_raw_axioms_standard=True,inherited_collector_disagreements=review['inherited_collector_disagreements'],own_disagreements=[]),walker_controls=dict(receipt='NLV_L105/receipt.json',count=8,exit=0),native=review['native'],predecessors=pins,retention=ret,peak_rss_kib=maxrss,swap=0,budget=dict(Lean_support_slots=140,Kani_slots=40,extraction=0,prelaunch_charged=['NLV_L002','NLV_L103']),closed_rows=[],row_root_emitted=False,ledger_delta=0,resource_targets_complete=False,physical_native_producer=False,trust='P6/D188/runtime/compiler/Std/allocator/Drop/Aeneas/ABI/source-to-ELF retained/reclassified, never removed; no new trust item',campaign='Not uniformly green: local failed drafts, prelaunch refusals, retired native timeouts, inherited collector disagreements and L121 packaging outer timeout are preserved.',packaging_replacement=json.loads((B/'NLV_PACKAGING_REPLACEMENT.json').read_text()),metrics_through_139=metrics,final_aggregation_receipt='NLV_L140/receipt.json')
(B/'NLV_AUDIT.json').write_text(json.dumps(audit,indent=2))
summary=f'''# NLV TX1 top handoff

Target NOT ESTABLISHED. TX1:094 remains OPEN; no row root or promotion.
The authoritative baseline stays ledger23 NLO580 CLOSED/0 QUALIFIED/19 OPEN.

## Checked support

L090 proves the complete20-occurrence SAME-argument source fold and parameterized
physical-cut fold, with full nominal source Result, every Err/fail/div prefix,
ordered attempted digest events and input/external frame chain. All20 source
step equations,38 frame/rank clauses, exact GExp structural identity and NHZ
induction pass. L099 proves SAME input/extents at every event and conditionally
applies CLOSED081 at those exact arguments. NLV_QueryCanonical derives all22
canonical queries from the SAME successful adopted prepare output.

NLV_Deployed fixes headline installation/digest slot43. Typed→SDK log lowering,
source trace existence and exact child source application pass. These are SOURCE
support, not a physical native invocation. NLV_State/Event and the stronger
resource087/094 schemas are proposed observations/targets, not certified heap/ABI
interpretations or complete resource packets. Completeness of nested ownership,
borrows and179 caller domains is still OPEN. Do not import them as full closure.

## Native and remaining obligations

40/40 Kani slots:19 local positives,18 matched assertion-failing negatives,
one compile failure,two retired90s timeouts. Exact KMX, offline frozen graph,
unchanged post-lock and deployed features validated before/after every run.
No multiplication/SHA/contract/static/Option<fn>-dependent credit. Transcribed
Log/reference windows are NOT a proof of the frozen tx1 body; native row credit0.

No full087 resource root/candidate was available at read-only research recheck.
The sibling source/value087 schema is explicitly weaker than the ledger; it is
not consumed as a full packet. Actual physical Cut production, complete lifetime/
cleanup, SAME081 Parsed/root/query provenance, CLOSED084 native installation,
full179 caller domains and post-query/flush checkpoint domains remain OPEN.
Read NLV_FAILING_STEP.md, NLV_REMAINING.md, NLV_ROWSPEC_REVIEW.md and
NLV_CALLER_CLAUSES.json. No success-only child premise or independent checkpoint
is hidden at a row root; no094 root exists. Full resource-schema completeness
itself needs review before use. Target remains100-bit PER-ATTEMPT,privacy,two tx.

## Audit and retained host

One combined import L100 passes with65 NLV modules,headline and126 NLV theorem
roots. L105 eight walker fixtures pass. NFX L106 exits0 over{review['modules']}
modules:0 dangling/conflicting owners/import mismatches,2420 compatible replicas.
All30 raw groups cover{review['required_roots']} roots; all raw axioms standard,
including every own theorem. The inherited raw/collector disagreements are
retained verbatim in NLV_AUDIT.json; their nonzero scope exits are not hidden.
L121 completed391 raw verdicts in178.275s but packaging hit180s (exit124).
L138 completed only missing packaging, never rerunning the walker; exit124 retained.
Peak RSS through retention{maxrss}KiB,swap0. Exact target/command/revision/source/
dependency hash/status/wall/RSS/swap/axioms are in receipts and attempts manifest.
Budget140 Lean/support slots (includes2 prelaunch refusals),40 Kani,0 extraction.
Final aggregation's own receipt is NLV_L140/receipt.json; no unchanged regression.

Host workspace `/home/dombarker/project-offloads/codex-cx-tx1-top-20261110`,
CARGO_TARGET_DIR=NLV_target,TMPDIR=NLV_tmp retained; own bytes{ret['own_host_bytes']}
(<30GB). Export NLV_exports_20261110; exact object hashes in NLV_EXPORT.json and
NLV_CLOSURE_PINS.json.xz. Seeded NLJ FIRST,NLC SECOND,ledger23 THIRD,then two
committed NLR interface objects read-only. All predecessor comparisons pass;
actual selected Aeneas objects are pinned. Never delete this cache/target/tmp.

Every scope admitted only at reservation exit0 AND allowed:true,free disk>=40GB,
MemoryHigh6G/Max8G/Swap0/Tasks64; Lean-M7000,optimized Rust,no raised limit.
No shipped files,keys,wallets,session-A/sibling worktrees,shared cache or pc/pv
worktree changed. Scratch-only cfg(kani) patch; no ELF rebuild trigger or new
ELF assertion. Frozen verifier/lock4bb3b3f5,Pool b936275465 and e0e49c34 owner pin;
section6 fields in NLV_FROZEN.json. No deployment/push,new trust row or pending
RuntimeCpiReadonlyEntry7 use. P6/D188 semantic transport is retained/reclassified.
'''
(B/'NLV_HANDOFF.md').write_text(summary)
with(B/'NLV_REMAINING.md').open('a')as f:f.write('\nFinal budgets:140/140 Lean-support slots and40/40 Kani,0 extraction. No early stop. Two Lean slots were charged prelaunch refusals; their exact causes/replacements are retained. Kani tail candidates small_window12 (one-write finish frame) and13 (checkpoint Vec output) were not submitted because40 native slots were exhausted; no claim is made from their source. Full post-flush/checkpoint domains still need Lean proofs as well as physical native association. Raw audit/retention use the remaining support slots; no root or row promotion is claimed.\n')
print(json.dumps(dict(status=audit['status'],roots=review['required_roots'],own_roots=review['own_roots'],peak_rss_kib=maxrss,swap=0,closed=0)))
