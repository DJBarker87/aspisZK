"""Produce a conservative per-record review, retaining provenance barriers explicitly."""
from pathlib import Path
import json,hashlib,subprocess,collections,importlib.util,lzma
D=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('c',str(D.parent/'pv-mf-20261029/PV_MF_check.py'));c=importlib.util.module_from_spec(s);s.loader.exec_module(c)
def read(p):
 q=D/p
 return json.load(lzma.open(str(q)+'.xz')) if not q.exists() else json.load(open(q))
stale=c.load('STALE.json');rows=read('rows9-input.json');trace=read('exact-traces.json');possible=read('candidate-traces.json');f=read('dlib-preflight-input.json')
byrecord=collections.defaultdict(set);potential=collections.defaultdict(set)
for t in trace:
 for h in t['hits']:byrecord[h['record']].add(t['id'])
for t in possible:
 for h in t['hits']:potential[h['record']].add(t['id'])
# These four stale pins occur in the verified final dlib audit packet; all four
# currently credited restoring theorems were checked in that exact cohort.
apaths={j['source_path'] for m,j in f['source_closure'].items() if not j.get('external')}
passes={json.load(open(p))['row']:json.load(open(p)) for p in sorted(D.glob('lean-*/result.json')) if json.load(open(p)).get('preflight_version')=='complete-h4'}
assert set(passes)=={'V187','V234','V235','V238'} and all(r['exit']==0 for r in passes.values())
tree={ln.split('\t')[1]:ln.split('\t')[0].split()[-1] for ln in subprocess.check_output(['git','ls-tree','-r','HEAD'],text=True).splitlines()}
results=[]
for i,t in enumerate(stale,1):
 p=t['path'];affected=sorted(byrecord[i]);poss=sorted(potential[i]);cls=None
 if p.endswith('/LOG.md'):
  cls='B';why='Historical definition-witness citation to D42/D188 prose; no Lean module compiles LOG.md. Exact old LOG blob is not a restoring theorem or native-source pin; narrative edits do not migrate a proof.'
 elif 'pv-dlib-20261028/' in t.get('receipt_path','') and p in apaths:
  cls='A';affected=sorted(passes);why='Consumed by the retained dlib final audit source closure (98 project modules), whose source blobs, object hashes, external leaves and original LEAN_PATH were verified before the four restoring-theorem checks. Old receipt pin superseded by the current-source final fingerprint.'
 elif affected or poss:
  cls='C'
  if '/pv-b3p6-' in p:
   why='Source-level import chain reaches '+','.join(affected or poss)+'. Required original cohort object is unavailable: /home/dombarker/project-offloads/codex-pv-b3p6-20261028/lean-objects/'+Path(p).stem+'.olean; no Install132 or Closure226 object was found in permitted Stream B caches. Actual compiled current-source cohort cannot be established under h6; rebuilding its project DAG is outside statement-check-only authorization.'
  else:
   why='Source-level candidate import/audit chain reaches '+','.join(affected or poss)+'. Actual compilation against this source variant is not established: the join audit has unresolved h7 source edges (enumerated per row in exact-traces.json.xz), and no complete original-cohort source/object/transitive-import fingerprint was recovered for this record. Current staged source alone does not establish its object provenance; no historical object is silently adopted.'
 elif p.endswith('.lean'):
  cls='B';why='Absent from every enumerated credited restoring-theorem and named audit import closure, including the conservative all-tracked-variant search. Receipt is historical/superseded or supports an uncredited row; no current closure use was found. External names terminate at the h4 authority, not similarly named tracked copies.'
 elif '/v241/' in p:
  cls='B';why='Historical op224 helper extraction/native phase; recount-9 V241 is OPEN. Neither its changing intermediate Rust harness nor its phase pin is a restoring theorem for a credited row.'
 else:
  cls='C';why='Non-Lean source/configuration pin. Imports cannot establish native-source consumption. The manifest provides no complete generation/structural/body-and-feature binding chain from this exact receipt pointer and old source hash to a credited restoring theorem. Current source file identity alone cannot resolve whether the old native/extraction association is required or superseded.'
 results.append(dict(record=i,category=cls,input=t,current_blob=tree.get(p),credited_rows=affected,possible_rows=poss,reason=why,result='PASSES' if cls=='A' else 'NOT RUN' if cls=='C' else 'NOT APPLICABLE'))
assert len(results)==764 and collections.Counter(t['status'] for t in stale)=={'STALE_OR_NON_FILE_HASH: review required':480,'STALE':284}
counts=collections.Counter(r['category'] for r in results)
(D/'classifications.json').write_text(json.dumps(results,indent=2)+'\n')
summary=dict(revision=f['current_revision'],counts=dict(counts),input_records=764,lean_invocations=8,native_scopes=1,kani=0,checked_closures=sorted(passes),failing_closures=[],unresolved=True,guard_sha256=hashlib.sha256((D/'PV_MF_check_dlib_host.py').read_bytes()).hexdigest())
(D/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
lines=['# D495 stale-source review','', '**Partial determination: '+str(counts['A'])+' A, '+str(counts['B'])+' B, '+str(counts['C'])+' C. No elaboration failure was observed; unresolved records prevent a clean bill of health.**','',
'Candidate/source revision `'+f['current_revision']+'`; branch `codex/pv-mfb-20261029`; exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-mf`. No source edits, proofs, package replay, native build, Kani, or wallet operations. V346 and privacy endpoint obligations remain open; no premise was removed or trust item added.','',
'Input is the exact ordered 764-record `../pv-mf-20261029/STALE.json.xz` (480 review-required, 284 STALE). Record numbers below are one-based array indices, so duplicates remain distinct. The authoritative recount input is the full rows9 at research `47f44e887a502ad865ca0635745eae7cc4ac7b3b`, not the manifest’s abbreviated historical export: `closing_statement9`, `closure_theorem`, `import_witnesses9` and native dispositions were retained. It credits 57 rows; V270 is an excluded formatter diagnostic with no restoring theorem, leaving 56 restoring theorems.','',
'| Input group | A | B | C | Total |','|---|---:|---:|---:|---:|','| Review required | 4 | 351 | 125 | 480 |','| STALE | 0 | 248 | 36 | 284 |','',
'## A: focused current-source checks','',
'The four dlib stale records (307–310: LengthEncoding, EncoderMutation, FinalizeParam, Forwarding) occur in the final dlib audit packet. Every one of its 98 project sources matches current candidate bytes. Before each check, the original object SHA and transitive import SHA were verified, terminating external leaves at the h4 recorded object hash. The same toolchain and original LEAN_PATH prefix were retained. Objects were read-only; only this job’s wrapper outputs were written. The wrapper contains only import, #check and #print axioms. Each distinct credited restoring theorem was checked once; the shared audit’s four stale records share those results.','',
'| Row | Restoring theorem | Env-J | Exit | Wall s | Peak RSS KiB | Swap | Result |','|---|---|---:|---:|---:|---:|---:|---|']
for row,p in sorted(passes.items()):
 n=p['attempt'];rec=json.load(open(D/f'lean-{n}/receipt/receipt.json'));th=next(x['closing']['theorem'] for x in trace if x['id']==row)
 lines.append(f"| {row} | `{th}` | {n} | {p['exit']} | {rec['wall_seconds']} | {rec['peak_rss_kib']} | {rec['swaps']} | PASSES |")
lines+=['','All four axiom audits return `[propext, Classical.choice, Quot.sound]`. Exact compiler output, preflight source/object maps, source revision and scope receipts are in `lean-69605`–`lean-69608`. The generic receipt runner writes an incorrect generic “N/A” axiom placeholder; each authoritative actual Lean axiom result is retained in that attempt’s `result.json` and `lean-output.log`. No inference is made from the placeholder. Caps: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000; admission and the in-scope barrier both passed.','',
'**Credited closures that FAIL: none observed.** This means zero checked elaboration failures, not that all credited closures survive.','',
'## C: why the decision remains incomplete','',
'V228 and V243 have real current-source import paths to the stale b3p6 modules, but their original objects have been removed. Read-only searches found no `PV_B3P_Install132.olean` or `PV_B3P_Closure226.olean` in permitted Stream B directories. The historical b3p6 cleanup receipt explicitly deletes `lean-objects`; later retained receipts are not proof that those objects still exist. A missing object is an environment/provenance barrier, not an elaboration failure, so these records are C rather than a fabricated FAIL.','',
'Older join audits have unresolved h7 edges including `AspisR1CircleFallback.RawCircleFallbackOutputBridge`, `AspisR1CircleSampleWrapper.Funs`, `AspisR1CircleSampleWrapper.RawCircleSampleActualSamplerCanonicalV1`, `AspisV8R19.SamplerClosureCircleSourceExecution`, and `ProverRwSampler.Funs`. The exact edge, source alternatives, row and chain are in `exact-traces.json.xz`. Same-named source paths or currently staged shared source hashes do not establish the complete original-cohort dependency fingerprint demanded by h6.','',
'Non-Lean stale source/config pins remain C where no exact old-receipt-to-current-restoration native binding chain is available. A Lean statement check cannot alone establish that a changed Rust body, feature profile or old harness certificate is the one consumed. The per-record pointer and old hash are preserved, rather than declaring these historical by filename.','',
'Budget used: **8/60 Lean invocations (four initial uncredited runs plus four corrected checks), 1/10 preflight-only native scopes, 0 Kani**. Further checks were stopped at source/cache preflight, not at a failed theorem. The remaining budget cannot repair missing h7 provenance or rebuild a deleted dependency DAG under the user’s statement-check-only restriction. Initial attempts 69600–69603 checked only external boundary hashes, so they are excluded from credit. The corrected wrapper verifies all 5,673 external hashes before Lean; its changed preflight supplies the missing evidence and justifies attempts 69605–69608. This is an environment/preflight correction, not an unchanged failed-proof rerun. Attempt 69604 initially received a quiet-window refusal (zero Lean invocations); the full cooldown/window was respected before reusing the unlaunched ID. After the quiet window, 69604 stopped before Lean because the corrected job wrapper used roots before initialization (NameError). Its failure receipt is retained; initialization was moved before verification, and corrected inputs were launched under 69605. The failed preflight scope counts conservatively as one native scope and zero Lean invocations. No full-manifest replay occurred. Failed-source guard SHA-256: `'+summary['guard_sha256']+'`.','',
'## Per credited row','', '| Row | Restoring theorem | Review disposition |', '|---|---|---|']
for t in trace:
 row=t['id'];cs=t['closing'];n=len(t['hits'])
 if row in passes:disp='PASSES; current dlib audit and source/object closure verified'
 elif not cs:disp='No restoring theorem: excluded formatter diagnostic; not an accepted native formatter closure'
 elif n:disp=f'C: {n} source-level stale-record matches; actual current-source cache/cohort not established'
 else:disp='No stale Lean-path match in enumerated closure; native-source C records are not discharged by this absence'
 lines.append('| '+row+' | `'+(cs['theorem'] if cs else 'none')+'` | '+disp+' |')
lines+=['','## Every stale record','',
'`classifications.json` is the machine-readable review with complete original records, hashes, current git blobs, row associations and reasons. `exact-traces.json.xz` preserves current-source import chains; `candidate-traces.json.xz` is an over-approximation used only to avoid false B exclusions. It does not select a cohort. B is an evidence-use classification, not an assertion that the stale pin itself became current.','',
'| Record | Class | Path | Receipt/pointer or historical row | Credited/possible rows | Result/reason |','|---:|---|---|---|---|---|']
for r in results:
 t=r['input'];ref=(t.get('receipt_path','')+t.get('pointer','')) or t.get('row','');rr=','.join(r['credited_rows'] or r['possible_rows']) or '—';why=r['reason'].replace('|','/');lines.append(f"| {r['record']} | {r['category']} | `{t['path']}` | `{ref}` | {rr} | {r['result']}: {why} |")
(D/'STALE-REVIEW.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(summary,indent=2))
