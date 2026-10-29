from pathlib import Path
import json,re,subprocess,hashlib,datetime
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-own-20261028'
rows=sorted([json.loads(p.read_text())for p in E.glob('lean-*/receipt.json')],key=lambda r:r['attempt'])
assert [r['attempt']for r in rows]==list(range(61700,61800))
allowed={'propext','Classical.choice','Quot.sound'}
def queries(text):
 return [' '.join(x.split())for x in re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",text,re.S)]
summary=[]
for r in rows:
 out=(E/f"lean-{r['attempt']}/output.log").read_text();q=queries(out)
 if r['exit']==0:
  assert 'sorryAx'not in out,r['attempt']
  for x in q:
   if '['in x:assert set(x.split('[',1)[1].split(']',1)[0].replace(' ','').split(','))<=allowed,x
 for tag in ['before','barrier']:
  assert json.loads((E/f"lean-{r['attempt']}/admission-{tag}.json").read_text())['allowed']is True
 summary.append({k:r.get(k)for k in ['attempt','module','target','exit','wall','peak_rss_kib','swap','source_revision','source_path','source_blob','source_sha256','deps_fingerprint','limits']}|dict(axioms=q,credited=r['exit']==0,raw_receipt=f"lean-{r['attempt']}/receipt.json"))
assert all(r['exit']==0 for r in rows[-3:])
assert len(queries((E/'lean-61798/output.log').read_text()))==116
native=[json.loads(p.read_text())for p in sorted(E.glob('native-*/receipt.json'))];assert len(native)==3
# Every actual admission after a refusal respects the complete cooldown.
refusals=[]
for p in E.glob('refusals/*/admission-*.json'):
 a=json.loads(p.read_text())
 if a.get('allowed')is False:
  stamp=datetime.datetime.fromisoformat(a['utc']).timestamp();refusals.append(stamp)
admissions=[]
for p in [*E.glob('lean-*/admission-before.json'),*E.glob('native-*/admission-before.json')]:
 a=json.loads(p.read_text())
 if a.get('allowed')is True:admissions.append(datetime.datetime.fromisoformat(a['utc']).timestamp())
for stamp in refusals:
 subsequent=[t for t in admissions if t>stamp]
 if subsequent:assert min(subsequent)-stamp>=180,(stamp,min(subsequent)-stamp)
(E/'combined-audit.json').write_text(json.dumps(dict(lean=summary,native=native,lean_starts=100,lean_pass=sum(r['exit']==0 for r in rows),lean_fail=sum(r['exit']!=0 for r in rows),kani=0,refusals=len(refusals),admission_and_cooldown_ok=True),indent=2)+'\n')
fp=json.loads((E/'final-fingerprint.json').read_text());assert fp['project_count']==89 and fp['external_count']==5673 and fp['external_ok']
(E/'COMMITS.txt').write_text(subprocess.check_output(['git','log','--oneline','6a2c273f22..HEAD'],text=True))
status={
 'V229':'Full Link representation/variant layout and padding abstraction; native in-place collector read/write/drop cursor, generation and scoped ownership invariant; every destructor/error/abort continuation; then compose PV_RDB2D_CollectorProgram.complete and its value law. This complete native-to-byte-world association was not proved.',
 'V230':'V229 association, plus actual deployed usize/u16 shift/OR/stack-array carrier association. The 544-byte POD free model and concrete MIR do not discharge those dependencies.',
 'V239':'Native sparse Vec initialized-length/header/byte/ownership instance; arbitrary monadic builder cardinality and raw ordered QM31 association; dense/sparse transport and public point/length at the consuming protocol call. The append draft is uncompiled and receives no credit.',
 'V178':'Compose the actual owned name/join source and cleanup into the shared byte/world relation, with source-complete diagnostic reachability and public provenance of every diagnostic argument/header/guard. Probe MIR moves String into Path::join<String>; its cleanup is in the callee, not an inline wrapper destructor.'}
for row,blocker in status.items():
 (E/(row+'.json')).write_text(json.dumps(dict(row=row,status='SUSPENDED',exact_blocker=blocker,native_consumed_law_established=False,new_endpoint_premises_removed=0,new_endpoint_premises_added=0,new_endpoint_premises_changed=0,witness_dependent_native_finding=False),indent=2)+'\n')
table='\n'.join(f"|{r['attempt']}|{r['module']}|{r['exit']}|{r['wall']}|{r['peak_rss_kib']}|{r['swap']}|"for r in rows[-3:])
peak=max(int(r['peak_rss_kib'])for r in rows)
report=f'''# Shared ownership interface — final report

**V229, V230, V239 and V178 remain SUSPENDED. No row restored, no checked witness-dependent native FINDING, no endpoint premise removed. Privacy target not yet established.**

Exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-own`, branch `codex/pv-own-20261028`, starting revision `6a2c273f22` (candidate `1a3cd3de26` plus parked world). New Lean prefix PV_OWN_; IDs61700–61799 only, audits61797–61799. [INTERFACE.md](INTERFACE.md) was committed in b00014f717 before any new Lean. [COMMITS.txt](COMMITS.txt) gives `git log --oneline 6a2c273f22..HEAD` through the evidence preparation; the final report commit follows.

## Checked progress and its limit

The80 new interface modules prove byte-range initialization/read uniqueness, out-of-range and disjoint-write frames, heap installation with both actual allocation sizes, move/take and unique-owner preservation, shared/exclusive borrow exclusions, checked store/move/drop preconditions, allocation success/null/failure/divergence post-worlds, actual-handler continuation threading, truncate representation, and concrete POD backing-store drop equations. Allocation identity retains generations; growth invalidates stale generations, preserves initialized prefixes and exposes uninitialized spare bytes. The reserve bridge **consumes** the existing complete PV_RDB1_V183 reserve law and its byte-prefix theorem, rather than assuming successful allocation or proving a second reserve family.

The world adapter retains W-CARRIER-1 process fields. Its frame equations describe the adapter, not native allocator/destructor purity. The public container relations, in PV_OWN_Reserve.lean, distinguish allocation-free zero-capacity Vec from allocated storage and require a String UTF8 encoding witness using the actual U8 codec. U16 has an injective little-endian codec. All21 Link kind variants and payload fields are retained; the schema script checks them against frozen source. The checked non-injectivity theorem explains why endpoint-only Link values cannot be a byte-refinement carrier.

These are **mathematical/model interface laws**, not a complete deployed-runtime refinement. The raw transformers are not runtime permission checks; CheckedAlloc/CheckedStore/CheckedMove/DropGate carry their preconditions. Scoped borrow release currently models a LIFO continuation. A native Link variant/padding codec and native lifetime/cursor association remain unproved. There is no universal Drop theorem. The old BoxAdequacy disjointness predicate reused the new request's size for existing allocations; the shared heap law uses each existing allocation's own size. This is an interface correction, not a counterexample to native allocation or a D159 witness pair.

## Consumers, in required order

'''+''.join(f'**{row} — SUSPENDED.** {blocker}\n\n'for row,blocker in status.items())+f'''The inherited row laws were read but no complete native consumer law was fabricated from them. Before: logical-cell/value/resource programs with unproved native ownership association. After: one checked shared byte/ownership algebra with the exact associations above still open. Endpoint premises removed/added/changed: **0/0/0**. No witness domain, observer, simulator, dictionary or failure event changed. Unclassified diagnostic/public-point provenance is suspension, not a checked witness-dependent finding.

## Source, MIR and trust

Native02 uses rustc1.94.1, deployed dependency versions and resolved feature union, release opt3, assertions/overflow checks off, panic unwind. It passes finite lifecycle checks at8 sizes and captures324 MIR files. Observed Link layout is size8/alignment2, kind offset4, producer0, consumer2; sparse tuple size24/alignment8. [drop-mir.json](drop-mir.json) and [drop-mir-audit.json](drop-mir-audit.json) retain exact Vec, String, Box and owned-join MIR and normal/unwind edges. Vec glue calls element-drop then RawVec cleanup; String delegates to Vec<u8>; Box drops pointee before allocator cleanup. The POD needs_drop checks pass. This is **deployed-configuration probe MIR and finite validation**, not the deployed client's complete callsite refinement or a structural K-1 substitute. Field source identity was supplemented after the native run and is explicitly labelled late; Link source was checked before it.

Every step resting on Kani, Aeneas or Charon agreeing on Rust semantics is **reclassification within existing tool trust**, never premise removal. No new extraction or Kani run occurred; no copy-dependent or function-pointer Kani PASS is consumed. (x') is not bypassed with another extractor. Compiler/MIR-to-executable D381/D386 remains retained. Under rdea-1, actual allocator outcomes given prior state, fresh aligned disjoint ranges, allocation/reallocation/deallocation and actual failure handlers remain under the existing runtime/allocator primitive item. Native typed stores, ownership and concrete continuation binding are not moved there. T remains exactly **entropy_law, entropy_kernel, observation**. E1/E2, real RunJoin, proof-account client routing and L1/L2/L3 remain obligations.

## Verification and resources

**100/100 Lean starts:91 pass,9 fail;3/60 capped native/housekeeping scopes;0 Kani.** Native01 failed on missing task input after a quoting error; native02 passed the optimized build/probe; native03 verified fingerprints and removed only own rebuildable caches. [combined-audit.json](combined-audit.json) and numbered raw receipts record exact command/target, exit, wall, peak RSS, swap, source revision/blob/SHA, dependency fingerprint and complete axioms output. Failed elaboration/recovery output, including sorryAx, earns no credit.

|ID|Exact target|Exit|Wall|Peak RSS KiB|Swap|
|---|---|---:|---|---:|---:|
{table}

All three final targets use source revision **e89db568e0ffa9436e763d528765603a5cd5685e**.61797 checks116 declarations and prints six complete root statements.61798's116 named axioms queries use only subsets of propext, Classical.choice, Quot.sound.61799's composed checked-store replay and reserve/collector/container root queries pass with the same allowed axioms. This is one focused model closure replay, not a full privacy endpoint or release manifest replay. Maximum Lean RSS is{peak:,}KiB; native build peak540332KiB; all swaps0. Every scope uses MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64; Lean-M7000, one own scope at a time.

All5673 external objects were verified before the first compile and rechecked before final audits. [final-fingerprint.json](final-fingerprint.json) verifies89 project objects, every direct/transitive project edge and the complete external cohort. No project object from another job was reused; the two world and four reserve dependencies were privately rebuilt from h5-selected tracked sources. No library was rebuilt or shared source/object overwritten. Private external selection repaired namespace-root and matching IR availability; those environment changes justify retries of unchanged Layout source after61789/61790. Other rejected sources were changed before retry. The final frozen manifest's SHA/blob metadata was regenerated at the committed freeze; audit source bytes were unchanged.

Three reservation refusals were uncharged and retried with the same ID only after the full180-second cooldown; combined audit checks this mechanically. No actual scope launched after allowed:false/nonzero admission or during cooldown. Own preparation errors consumed no Lean ID: a missing dependency before61704, the audit queue's focused-ID guard, and two duplicate wrapper requests for already-successful61797/61798. The wrapper blocked both duplicates before Lean. Original successful receipts and prevented-start logs are retained. The initial ID scan covered direct job receipt names and shared sent files; the supplementary final scan covers nested receipt trees too.

[cleanup.json](cleanup.json) records89 private object files (5721784 bytes),21987 own links unlinked without following targets, and203962804 Cargo-target bytes removed. Sources, MIR and raw evidence remain. No wallet/account key was created, removed or modified; no other job directory was changed. No crates/programs, protected soundness file, observer, simulator or dictionary changed; no XR imports, new axioms, sorry/admit/native_decide/implemented_by or cap increases. No file over20MB is committed. No push or merge was performed.

Stopped at the100-start Lean budget. **Next deliverable:** the native V229 Link codec and in-place read/write/drop cursor and ownership refinement into this interface, preserving all variant data and continuations; only then compose the existing resource-program/value law and reconsider restoration. The uncompiled append draft is explicitly retained under unsubmitted/ and is not imported or credited.
'''
(E/'REPORT.md').write_text(report)
print('Wrote combined audit and report; all four rows SUSPENDED')
