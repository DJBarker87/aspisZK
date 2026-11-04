"""Render the row inventory and append only the Recount13 ledger section."""
import json,re
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent
rows=json.loads((P/'rows13.json').read_text());tot=json.loads((P/'totals.json').read_text())
lines=['# Recount 13 2026-11-04 (B)','','Target not yet established. Same407 historical meanings, guards, quantifiers and residuals; rows13.json overlays its explicit rows12.json historical links. Import membership is not discharge. One new named below-endpoint interface premise; no new counted row.','','| Row / class / name | Status12 →13 | OPEN bucket | In headline closure? | Tool trust | Derivation and residual |','|---|---|---|---|---|---|']
for r in rows:
 vals=[r['id']+' / '+r['recount13_class']+' / '+r['name'],r['recount12_status']+' → '+r['recount13_status'],r['dependency_bucket'] or '—',r['in_headline_closure13'],r.get('tool_trust10','Prior named trust retained'),r['recount13_basis']+' See recount13/rows13.json#'+r['id']]
 lines.append('| '+' | '.join(str(v).replace('|','\\|').replace('\n',' ') for v in vals)+' |')
(B/'ROWS13.md').write_text('\n'.join(lines)+'\n')
ledger=Path('design/PRIVACY-LEDGER-20261026.md');text=ledger.read_text();assert '## Recount 13 2026-11-04 (B)' not in text
prior=text.split('## Recount 12 2026-11-04 (B)')[1];table='\n'.join(x for x in prior.splitlines() if x.startswith('|'))
newcol={'Rows':407,'T':3,'P':400,'C':4,**tot['statuses']}
tablelines=[]
for ln in table.splitlines():
 label=ln.split('|')[1].strip()
 if label=='Inventory / status':val='Recount 13'
 elif label.startswith('---'):val='---:'
 else:val=str(newcol[label])
 tablelines.append(ln.rstrip()+' '+val+' |')
section="""

## Recount 13 2026-11-04 (B)

Independent immutable-source/statement/receipt recount from research33b7941bbab;
[all pins](../evidence/privacy-recount-20261026/recount13/pins.json).
The candidate's shared origin head is d4ed1ba89f, independently confirmed by
read-only ls-remote; stale local8e450dab558 is excluded. Nine requested live
worker heads are frozen, including own2b6b821de735. Later work is excluded.
All407 historical row scopes and residuals retained. **Target not yet established.**

"""+ '\n'.join(tablelines)+"""

Explicit row status changes:

- **V177/V180: OPEN a → CLOSED-ON-CANDIDATE**, exactly their former C044-backed
  bounded PathBuf deref/as_ref source/model P6 scopes (byte lengths≤4, arbitrary
  checked full-width get query). Both had exactly C044 withheld in Recount12;
  no stronger native/std transfer or whole privacy closure is restored.
- No other status/class changes; OPEN66 = a4/b58/c3/d1; REDUCED176,
  EVIDENCED14, CLOSED-ON-RESEARCH87, CLOSED-ON-CANDIDATE64. P400/C4/T3.
  Historical consumer-root membership is research160/candidate103/neither144;
  restored closure-source witnesses for V177/V180 are neither. Membership
  remains distinct from discharge.

Explicit credit changes, independently confirmed from raw retained traces:

- **RESTORE C044:** positiveK93512 passes; controlK93502 at lib.rs:74 fails
  intentionally inverted len!=r.len on equal0 lengths, n=i=0; checked get is
  None. Complete-file SHAe2e80df1364f5c614b9880d76506e32f622d5e6dd6cffdd5c1a6594352b41a15.
- **RESTORE C084:** positiveK93503 passes; K93504 at lib.rs:145 compares
  byte65 with byte65, index0, two-byte String/Path; intended inequality fails.
  Historical bounded stubbed scope only; V179's structural support is unchanged.
- **RESTORE C088/C089:** positivesK93505/K93507 pass; controlsK93506/K93508
  trace sealed.rs:105/123 scalar block-length inequalities (0=0;64=64) into
  assert_failed_inner at panicking.rs:439. This resolves the old generic panic
  placeholder. No coordinate dereference causes those failures. Original
  bounded stubbed lo/hi scopes only; **C002 stays SUSPENDED**. V233's separate
  typed structural consumed_instance and complete-Result qualifications remain.
- **RESTORE K93109/K93110/K93111:** K93513/K93510/K93511 each has one positive
  pass and two intended controls failing at indexed.rs:42/44 (value/frame XOR1).
  Logical offsets remain u128; physical pointer slots are0/1. Original two-place
  projection only; original ptr.add/allocation/OWNER association remains OPEN.
- All ten accepted controls fail for their intended reason; none obtains its
  failure through48-bit offset aliasing. Raw reachability-probe failures are
  driver instrumentation, separately recorded, never called program failures.
  Source hashes, original pins, commands, symbol maps, features/profile, tool
  hashes, admissions and wall/RSS/swap receipts are retained. Peak3126844KiB,
  swap0 across provider runs. Metadata-onlyK93509 and capture diagnostics
  K93500/K93501 earn no positive credit. Kani was not rerun here.
- Historical305-credit inventory returns to **26 RESTORED/81 UNAFFECTED/
  195 SUSPENDED/3 WITHDRAWN**. The three K931xx gates are separate. Original
  bounds, K-1/K-2/K-3, KMX, std parity/k''' structural qualifications and V370
  remain. C051/C053/C163/C164 remain restored; C156 remains suspended.

Explicit premise/interface and status-note changes:

- **D653: ONE NEW NAMED PREMISE BELOW THE ENDPOINT:**
  `PV_OWN2_FreshAllocation.FreshAllocationValidity resources granted s` at
  own2b6b821de735, [source and receipt audit](../evidence/privacy-recount-20261026/recount13/status-audit13.json).
  Before: arbitrary complete allocator replies with no named freshness-validity
  relation. After: at a reached OWNER pre-state, successful non-null positive-
  size malloc/calloc/posixMemalign replies lie in externally interpreted granted
  regions and are disjoint from live nonempty positive-width Owned ranges.
  This is an **undischarged rdea-1/V370 world-answer obligation**, not T and not
  an added endpoint premise. Null/zero/error/div/fault/pending branches stay;
  realloc is not classified as fresh. clone_disjoint and granted_contains
  derive consequences conditional on it and supplied resolved headers/places.
  No new counted row; V370 and native OWNER/source7 installation remain OPEN.
- **PV_OWN2_Codec: proved interface, no row closed.** Fixed partial M31/U32,
  QM31 and WideExact decoders at widths4/16/32 accept every initialized byte
  image, including noncanonical raw representatives, reject absent/nonbyte
  cells, and relate supplied OWNER places to world.memory. Typed copy results
  consume OriginalCopyTyped.decoded_element at supplied full bases and explicit
  separation. Valid/Pending/OwnedAt and unchanged D602 null-handler compatibility
  hold. Physical Rust-layout/native-place association remains unproved. Reused
  raw93690:35 roots, zero unresolved, raw/summary agreement, standard axioms;
  exit0,wall4.62s,peak6402064KiB,swap0,source4e4154293d0299152c1ab1a7caeea35ea80ba0b0.
- **D646–D649:** stx and stxb paused on the shared erased-activation/place
  obstruction; source8/source13 length/model progress does not close a parent.
  stx is reactivated only for the D651 instrumented route; own2 waits for places.
  stxb raw92995 has46 roots, not a native OWNER installation or row closure.
- **D651/stx-2:** authorized translator-generated call-entry/local-binding/
  return-place/aggregate-move instructions and a NEW instrumented machine need
  operational erasure/simulation preserving native events/fileTrace/countTrace/
  timeTrace/oraclePrefix, every failure/pending branch and post-world, with
  explicit administrative-step fuel accounting. Original places must be derived
  from activation/native reply, not chosen or supplied by receiver equality.
- **D656/stx-2': pending translator patch, no row change.** The fresh frozen-
  source library probe exposes TrivialClone::to_vec and native copy operands
  Local5/Local6/Local3, but unmodified ae1-2 rejects CopyNonOverlapping before
  lowering. Full deployed-route parity is not established. The permitted patch
  must have a pinned hashed diff/binary, option-off byte identity for the
  COMPLETE existing extraction cohort, and option-on native instructions with
  local/call identity. Record it as a **modification of the existing Aeneas
  tool-trust item**, not a new T field; owner-packet notice precedes adoption.
  No credited source at these pins cites a patched translator. Instrumentation,
  erasure and source7 original-place derivation remain pending/unproved.
- **D650:**27/217 local conditional caller certificates covering73 sites;
  raw92898 has292 roots, standard axioms, exit0,wall9.302s,peak4677564KiB,swap0,
  source19a84dd2ce50bc93fd42aca98c2818947cd33047. Compile-only92897 is not a raw
  audit; K93303 timeout and stoppedK93309 earn no credit. NativePending,
  NativeFault, NativeEffects, ResourceTimingIndependence and concrete OWNER
  obligations stay named. No original-entry/ops/opaque/DeployedWrapper557 or
  V241/V244/V245 closure. Later pinned family packages remain conditional.
- **D641:** D640's pending timing-window sentence is superseded: final-client
  N91120 already passed in D590 and adoption is D591. No timing rerun is needed
  or performed. D643/D647/D652/D654 thread-line fragments close no row;
  ordered_families_spawn_prefix_linear and the four D625 thread contracts remain
  OPEN named obligations. D602 abort qualification, l3-2 source projections,
  separate V370/L3 pairing residual and all other Recount12 qualifications stay.

[ROWS13](../evidence/privacy-recount-20261026/ROWS13.md),
[method](../evidence/privacy-recount-20261026/recount13/METHOD13.md),
[per-credit raw-trace check](../evidence/privacy-recount-20261026/recount13/k4-restore-check.json)
and [totals](../evidence/privacy-recount-20261026/recount13/totals.json) record
exact scoped dispositions. #print axioms is SUMMARY-BASED; retained NEP raw
walks are separately labelled, with hard errors on unresolved constants.

Validation here is inspection-only: Lean0/40,Kani0/0,Env-J93800–93839 unused;
no new proofs, host scopes, full replay, unchanged regression, release/source
edit, key action or push. Endpoint premises removed/added/weakened0/0/0;
**one new named interface premise below the endpoint**. T remains exactly
entropy_law,entropy_kernel,observation; simE/full observer/bound/domain/bad event
unchanged. Actual OWNER/world association, op227/op257, E1/E2, source/physical
side-channel links, native integration, event acquisition and joint simulation
remain open. Next: pinned translator patch and complete default-mode identity
gate before erasure, native places and source7 interface composition.
**Target not yet established.**
"""
ledger.write_text(text+section)
print('Rendered407 rows; appended Recount1–13 totals and explicit changes')
