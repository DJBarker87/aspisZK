from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent
ats=list(map(json.loads,(E/'NJN_ATTEMPTS.jsonl').read_text().splitlines()));assert len({r['attempt'] for r in ats})==len(ats)
kan=[r for r in ats if r['kind']=='kani'];formal=[r for r in ats if r['kind']!='kani' and r['kind']!='extract'];extract=[r for r in ats if r['kind']=='extract']
assert len(kan)==70 and len(formal)==30 and len(extract)==1
rows=[]
for r in sorted(kan,key=lambda x:x['attempt']):
 a=r['attempt'];log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode();cls='UNRESOLVED'
 if 'timed out' in log:cls='TIMEOUT_NO_CREDIT'
 elif 'VERIFICATION:- SUCCESSFUL' in log:cls='NATIVE_PASS_SUPPORT_ONLY'
 elif 'VERIFICATION:- FAILED' in log and 'Failed Checks:' in log:cls='SEMANTIC_FAIL'
 elif 'could not compile' in log:cls='COMPILE_REJECTION'
 elif 'AssertionError:' in log:cls='PREFLIGHT_REJECTION'
 check=re.search(r'Failed Checks: (.*)',log)
 rows.append(dict(attempt=a,target=r['module'],classification=cls,exit=r['exit_status'],failed_check=check[1] if check else None,wall_seconds=r['wall_seconds'],peak_rss_kib=int(r['peak_rss_kib']),swaps=int(r['swaps']),source_revision=r['source_revision'],source_hashes=r['source_hashes'],CARGO_TARGET_DIR=r['env']['CARGO_TARGET_DIR']))
assert all(r['classification']!='UNRESOLVED' for r in rows)
(E/'NJN_NATIVE_RESULTS.json').write_text(json.dumps(dict(results=rows,complete_sdk_certificates=0,new_composed_rows=0,note='PASS is supporting native evidence only. Exact pairings and limitations in NJN_LAWS/CERTIFICATES.'),indent=1)+'\n')
# Verify complete current root list, successful focused sources and raw audit.
roots=json.load(open(E/'NJN_AUDIT_ROOTS.json'))['groups'][0];assert len(roots)==47
log=lzma.decompress((E/'NJN_L027/stdout.log.xz').read_bytes()).decode()
assert 'sorryAx' not in log
for root in roots:assert root in log,root
scan=json.load(open(E/'NJN_AUDIT.json'));assert not any(scan['scanner'][k] for k in ['dangling','incompatible_owners','import_mismatches'])
# All selected current theorem modules have an exact source match to a PASS.
mods=re.findall(r'^import (NJN_\S+)',(E/'NJN_COMBINED_IMPORT.lean').read_text(),re.M)
for m in mods:
 h=hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest()
 assert any(r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values() for r in formal),m
for p in E.glob('*-admission.json'):
 x=json.load(open(p));assert x['exit']==0 and x['reservation']['allowed'] is True
 assert sum(any('NJN_' in v for v in z.get('processes',[])) for z in x['reservation']['populated_scopes'])<=1
locks=list(E.glob('NJN_K*-lock-check.json'));graphs=list(E.glob('NJN_K*-graph-check.json'))
assert len(locks)==69 and len(graphs)==69
assert all(json.load(open(p))['unchanged'] for p in locks)
assert all(json.load(open(p))['graph_matches_frozen'] for p in graphs)
assert all(int(r['swaps'])==0 for r in ats)
summary={c:sum(r['classification']==c for r in rows) for c in sorted(set(r['classification'] for r in rows))}
x=dict(native_attempts=len(kan),formal_attempts=len(formal),extractions=len(extract),native_classes=summary,peak_rss_kib=max(int(r['peak_rss_kib']) for r in ats),scope_wall_seconds=sum(r['wall_seconds'] for r in ats),swap=0,roots=47,complete_sdk_laws=0,new_composed_rows=0,target_established=False,matched_frozen_graphs=len(graphs),unchanged_post_run_locks=len(locks),full_combined_audits=2,source_pin_check='NJN_L030/receipt.json',cleanup='NJN_L031/receipt.json',raw_log_normalization_corrections=len(json.load(open(E/'NJN_RAW_LOGS.json'))['normalized_log_corrections']))
(E/'NJN_FINAL_CHECK.json').write_text(json.dumps(x,indent=1)+'\n')
export=json.load(open(E/'NJN_EXPORT.json'));host=json.load(open(E/'NJN_HOST_END.json'))
(E/'NJN_HANDOFF.md').write_text(f'''# NJN entry SDK handoff

**Target not yet established. Incomplete SDK-law return; no complete reusable SDK
certificate and no ledger promotion.** Branch codex/cx-entry-sdk-20261107; no push.
Baseline NJK ledger14 remains438 CLOSED /0 QUALIFIED /161 OPEN.
Headline AspisR1.RPx_Deployed.deployed; frozen Rust
4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Frozen3, L154 parameter,
narrowed D188, 100-bit PER-ATTEMPT soundness, privacy and two transactions retained.

## Established support and exact limits

Nine mathematical modules,46 support roots plus the headline, compile together
on NJK_COMBINED_IMPORT. Complete local transition/frame, same-cell drop, copy
range/drop consequences over canonical KMX induction, full Clock reply/error
model and PDA validation/status/abort model are checked. These are HAND MODEL
facts, not extract(f_ref)=law or actual SDK substitution. The pointwise Live
predicate lacks a global unique-token/shared-count invariant (NJN-F2).

Native support: safe guard-count partitions0..7 execute actual AccountInfo calls
and actual typed guard return/move/drop, with corrupt-counter/wrong-cell controls;
the 1768-byte exclusive-copy arbitrary window/outside frame/metadata and Drop
pass with corrupt-value/frame controls; builtin/custom ProgramError conversion,
PDA error conversion, direct Borsh byte coordinate and native Clock::default's
five zero fields/40 zero bytes/alignment8 have matched controls. Wrapper
postconditions and fixed input domains remain narrower than a full owned-heap
SDK law (NJN-F1). No Option<fn>, writable static, field multiplication, digest
unwind, SHA/curve unwind or unchecked SDK logging stub is used.

The ONE extraction supplied all twelve owned references, including account/
heap/guard/data carriers and concrete syscall errors. Charon exit0, Aeneas exit2
at guard drop, InterpBorrows.ml:2731; no Lean output. The original input/LLBC/pins
and failure are retained. No retry; the outlining patch is PROPOSED, untested.
The full ProgramError and Borsh contract shapes and large-payload borrow-conflict
interfaces timed out; smaller independent interfaces are explicitly separate
support. They do not erase those failures. NJN_FAILING_STEP records all repairs.

No newly complete law licenses an NJD stage cut. NJD_K038 and unchanged timeout
shapes were not rerun. Fifteen entry rows wait on the driver spine or independent
decoder/authentication children under(as); observers are already CLOSED.
NJN_LAWS/NJN_STUBS/NJN_CERTIFICATES give statements, domains, native pairings and
Lean roots; NJN_CUTS and NJN_REMAINING inventory every unclosed member.

## Validation and resource accounting

Budget used:70/70 native attempts,30/70 non-extraction formal scopes,1/1 extraction.
Formal use is below80%; this is NOT exhaustion or a claim every possible model
lemma is impossible. The required equalities concern an emitted full carrier
that does not exist after L001; full global ownership and native same-heap/frame
interpretation also remain missing. Member-by-member reasons and which parts
still need native verification/emission are in NJN_REMAINING. Further generic
frame wrappers do not discharge these concrete obligations.

Native outcomes: {json.dumps(summary,sort_keys=True)}. No timeout or memory stop
was rerun unchanged; no cap/timeout increase. Exact canonical KMX patch/body pins
and matched controls are recorded; copy-dependent old passes are support only.
All69 runs that reached the graph gate match the frozen graph and retain the
frozen lock afterward; K009 stopped before metadata/Kani. Actual reached SDK
source versions/bytes and inherited launcher identity verified in L030.

Two combined audits only. Final L026/L027/L028:47 raw roots, standard axioms only;
scanner15407 modules,717739 declarations,25507068 references,zero dangling,
incompatible owners or import mismatches. Eight fixtures/mutations passed in
same compiled proof binary. Hardened walker source identity and object pins in
NJN_WALKER_PIN. Full selected closure pins32000 objects/sidecars. Focused cached
cohort, not a cold release rebuild. Every receipt records exact argv,target,
revision/source/dependency pins,exit,wall,RSS,swap and printed axioms (native N/A).
All admissions exit0 AND allowed:true; caps6G/8G/swap0/tasks64,Lean-M7000,
optimized/offline Rust,own CARGO_TARGET_DIR. Admission snapshots never contain
more than one other own populated scope. PeakRSS{x['peak_rss_kib']}KiB;
aggregate scope wall{x['scope_wall_seconds']:.3f}s;swaps0. Raw byte logs preserved.

## Retention, assumptions and next deliverable

Own workspace /home/dombarker/project-offloads/codex-cx-entry-sdk-20261108;
CARGO_TARGET_DIR=NJN_target inside it. Seeded NJH retained export FIRST407664
bytes, then NIV2265348 bytes, individual hashes retained. Own export
{export['path']}
({export['bytes']}bytes,tree{export['tree_sha256']}) retained; prepend it and
NJN_seed to the L026 LEAN_PATH. Own seed/objects/cache and source snapshots
retained. Cleanup verified exports and removed only owned target/native binaries
and solver scratch; free bytes{host['free_bytes']}. No key created or removed.

No shipped source or existing proved module changed. No ELF rebuild trigger;
inherited,not newly reproduced:default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No sessionA/sibling worktree touched. No new trust, no premise discharged;
option-A P6/D188 transport remains reclassification, never removal. No PDA
value row, RuntimeCpiReadonlyEntry7 or free operation dictionary at a root.

Next: complete the valid global carrier interpretation, repair/split full
reference emission under a fresh extraction allowance, then actual SDK and
Clock/PDA syscall ABI/frame contracts. Only then instantiate SDK logging stubs
in the source-ordered NJD cuts. These are missing deliverables, not assumed laws.
''')
print(json.dumps(x,sort_keys=True))
