"""Render reviewed atomic-law correspondence from complete kernel statements.
No prover replay; classifications and semantic correspondence are explicit audit
judgments. Counts, field extraction, row diff and owner tags are mechanical.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,re,subprocess
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cons=ROOT/'evidence/consolidate-20261026/Cons_premises.json'
x=json.loads(cons.read_text())
t2r=json.loads((ROOT/'evidence/tx2-resume-20261026/T2R_premises.json').read_text())
log=(OUT/'Rc2_022/stdout.log').read_text()
assert '@AspisR1.Rc2_Top.deployed' in log and '@AspisR1.Cons_Top.deployed' in log
assert '∃ f s, ⋯' not in log # Only proof-irrelevant subtype witnesses may be elided
assert len(json.loads((OUT/'Rc2_022/receipt.json').read_text())['print_axioms'])==6
# Extract newly printed structures verbatim, including shared quantifiers/guards.
catalog={}
for block in re.split(r'(?=^structure )',log,flags=re.M):
 if not block.startswith('structure '):continue
 name=re.match(r'structure (\S+)',block)[1]
 fields=block.split('fields:\n',1)[1].split('constructor:',1)[0]
 catalog[name]={'evidence':'Rc2_022/stdout.log','fields':fields,'field_names':re.findall(r'^  ([\w.α-ωΑ-Ω]+) :',fields,re.M)}
assert len(catalog['AspisR1.S2Trust.S2TrustedSdkBorrow']['field_names'])==15
assert len(catalog['AspisR1.DrvC_Installation.Configuration']['field_names'])==9
assert len(catalog['AspisR1.S2W_D189Wrappers.Allocator']['field_names'])==2
(OUT/'Rc2_field_catalog.json').write_text(json.dumps(catalog,indent=2,ensure_ascii=False)+'\n')
# Changed conclusion expansions plus exact named-binder source statements.
for token in ['NP6_ClaimsRun.Content','NP6_ParsedClaims.Content','NP6_Constructors.Contents','Rc2_Protection.Facts','Rc2_Events.Facts']:
 assert 'AspisR1.'+token in log,token
source=(ROOT/'lean/Rc2_Top.lean').read_text()
result=(ROOT/'lean/Rc2_Result.lean').read_text()
assert 'TwoTransactionLaw' not in source+result and 'Rc2_History' not in source+result
assert 'Frozen3' not in source+result
assert 'PoolT_Write.accepted_verifier_writes_copy' in source
assert 'T2R_Top.deployed' in source and 'Rc2_Install.select c reservation' in source
# Read T2R evidence as checked correspondence, never subtract a worker headline.
removed={r['id']:(r['discharge_theorem'],r['audit_reason']) for r in t2r['rows'] if r['scope']=='removed by T2R'}
assert set(removed)=={'L085','L086','L087','L122','L123','L124','L126','N116'}
removed['L177']=('NP6_SOURCE_CERTIFICATE; Rc2_Install.standard/dictionary; Rc2_Base.strengthen',
 'Selected safe reserve/intoBox interpretation and full scoped shipped Claims helper certificate; arbitrary free std slot replaced explicitly. Existing allocator/runtime/extraction/artifact boundaries retained.')
rows=[];diff=[]
for old in x['rows']:
 r=dict(old)
 if r['id'] in removed:
  th,reason=removed[r['id']]
  diff.append({**r,'status':'removed','reason':reason,'checked_result':th})
  continue
 r['status']='still present';r['evidence']='Rc2_022/stdout.log; named-binder source and unchanged inherited field inventory'
 if r['id']=='L179':
  r['blocker']='NP6 closes Claims-local allocation/ownership/cleanup/frame only. Concrete whole library/native frame, allocator interpretation and source-to-artifact association remain outside that helper scope.'
 if r['id']=='L180':
  r['blocker']='L094-L096 remain: owner must clarify the physical two-transaction security game and adopt or replace TwoTransactionLaw; prove ordinary-key eligibility, physical identity, final parent success and source-ordered action association.'
 rows.append(r)
 diff.append({**r,'reason':r.get('blocker',r.get('meaning','Retained family on the selected dictionary.'))})
# New guards in CPR protection are inventoried exactly as conditional laws, not
# smuggled into data structures. They do not gate the inherited conclusions.
extra=[
 ('keyLaw','(DrvC_Installation.sdk selected).op36 = Hist_Authority.keyEq',
  'Prove the installed op36 key-equality/source interpretation; adapter remains data-only and arbitrary. Needed for new bank effect/protection conclusions.'),
 ('owner','(before.cells key).owner = program',
  'Associate an arbitrary protected-bank key with the verifier program owner. The accepted writer derives this in its scoped bank model; the top does not identify every arbitrary before/key with that writer.'),
 ('marker.nonempty','0 < (before.cells key).data.val.length',
  'Prove nonempty data at the arbitrary protected-bank key; first conjunct of Initialized. Accepted writer shape does not identify the universal before/key.'),
 ('marker.tag','Slice.index_usize (before.cells key).data 0 = ok 82',
  'Prove the exact initialized tag at that arbitrary protected-bank key; second conjunct of Initialized. Accepted writer derives its local marker, but this bank/key association remains.'),
 ('positive','0 < before.lamports key',
  'Supply positive lamports for the protected key; bank model protection excludes zero-balance deletion. No runtime persistence law is used to prove this guard.')]
for n,(name,meaning,blocker) in enumerate(extra,1):
 r=dict(id=f'Rc2_P{n:03}',name='protection.'+name,meaning=meaning,classification='P',owner='lead',scope='actual antecedent',status='newly present',blocker=blocker,definition='lean/Rc2_Protection.lean#Facts',evidence='Rc2_022/stdout.log',role='guard only of added bank-model conclusion')
 rows.append(r);diff.append({**r,'reason':blocker})
assert len(diff)==len(x['rows'])+5
# Tags refer to pending owner routes, not claims that adoption suffices to prove
# each tagged row. Multiple tags can apply; list all original session A rows.
a={'L157','L159','L181','L182','L185'}
b={'L094','L095','L096','L180'}
c={'L097','L098','L129','L130','L131','L132','N115','L165','L168'}
# These lead rows consume S1/S6 binding or S3/S4 source/model interpretations.
for r in rows:
 tags=[]
 if r['id'] in a:tags.append('a: frozen3 adoption (candidate route; no closure credit)')
 if r['id'] in b:tags.append('b: runtime law + contract-game clarification')
 if r['owner']=='session A' or r['id'] in c:tags.append('c: session A source/binding rows')
 r['owner_waits']=tags
for d in diff:
 if d['status']!='removed':d['owner_waits']=next(r['owner_waits'] for r in rows if r['id']==d['id'])
def counts(rr):
 return dict(rows=len(rr),classes=dict(Counter(r['classification'] for r in rr)),owners=dict(Counter(r['owner'] for r in rr)),by_owner={o:dict(Counter(r['classification'] for r in rr if r['owner']==o)) for o in ['lead','session A','external']})
scopes=['actual antecedent','deployment only','deployment alias']
summary={s:counts([r for r in rows if r['scope']==s]) for s in scopes}
summary['all retained audit rows']=counts(rows)
summary['deduplicated actual plus non-alias deployment']=counts([r for r in rows if r['scope']!='deployment alias'])
assert summary['actual antecedent']['classes']=={'T':82,'P':171}
assert summary['actual antecedent']['owners']=={'external':85,'lead':23,'session A':145}
lead=[r for r in rows if r['owner']=='lead' and r['classification']=='P' and not r['owner_waits']]
leadcounts={s:len([r for r in lead if r['scope']==s]) for s in scopes}
leadcounts['deduplicated']=sum(v for s,v in leadcounts.items() if s!='deployment alias')
leadcounts['all audit rows']=len(lead)
# L174 already absent from Cons: cannot remove it twice. L179 is broader than NP6.
originaldiff={r['id']:r for r in x['diff']}
assert originaldiff['L174']['status']=='removed'
result=dict(actual_theorem='AspisR1.Rc2_Top.deployed',method=__doc__,baseline=str(cons.relative_to(ROOT)),baseline_sha256=sha(cons),statement_sha256=sha(OUT/'Rc2_022/stdout.log'),counts=summary,lead_not_waiting_on_owner_routes=leadcounts,lead_not_waiting_ids=[r['id'] for r in lead],rows=rows,diff=diff,removed=list(removed),newly_present=[r['id'] for r in rows if r['status']=='newly present'],historical_L174='Already removed in Cons; strengthened by SAME-run NP6 Contents. No second subtraction.',L179='Partially scoped Claims frame derived; broader row retained.')
(OUT/'Rc2_premises.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
# Preserve all previous ledger text byte-for-byte. Re-running replaces ONLY this
# job's newly appended section, never a predecessor's section.
marker='\n## Recount on Rc2_Top (2026-10-26)\n'
doc=ROOT/'design/PREMISE-LEDGER-20261025.md'
original=doc.read_text().split(marker)[0]
text=marker+'''
**Actual theorem `AspisR1.Rc2_Top.deployed`; S2 OPEN, target not yet established.**
Branch `codex/cx-recount2-20261026`. Evidence and reproducible audit:
`evidence/recount2-20261026/Rc2_premises.json`, `Rc2_recount.py`,
`Rc2_022/stdout.log`, `Rc2_validation.json` and `Rc2_HANDOFF.md`.

This applies Ledger_003–005 and Cons's counting method to the complete actual
top and its factored conclusions: atomic conjunctive leaves, quantified law
families, SAME existential witnesses/guards, shared-dictionary deduplication.
The fresh successful kernel transcript prints both Cons and Rc2 statements,
Rc2_Result/Base/Events/Protection, NP6 contents and selected std dictionary,
T2R finish/ten/caller/continuation/acceptance, and retained SDK/std/allocator/
entry/extraction/owner structures. Rc2_field_catalog mechanically extracts the
printed structures. Preparation/query/geometry nested fields are freshly printed too; the unchanged
Cons_008/010 and Ledger_003–005 inventories are retained as the before evidence,
with source hashes checked against the same repository baseline; no passing import is credited as a proof of those
fields. The renderer makes explicit reviewed correspondence/classification
judgments, then mechanically enumerates rows/diffs/totals; it is not a logical
discharge checker. The baseline is Cons_premises.json's 281 retained rows, not
its already-removed historical rows. All 281 plus five new guards are accounted.

Selected composition: T2R's unchanged frozen parameters and source-selected
TX2 reader, NP6 initial/pending and parsed Claims content, exact PoolT accepted
copy plus metadata/other-cell frame, CPS source-bank events, CPP atomic ordered
oracle-log preservation, CPR rollback and guarded bank protection. Every
accepted cut/run/Claims/TX2 witness remains shared. The source-bank recorder is
parameterized by arbitrary initial/actions, and its saved value is the SAME
accepted TX1 return. No physical validator trace is inferred from that equality.

`Rc2_Install.select` explicitly replaces only the free Claims std slot by
NP6_StdModel.calls reservation, preserving the other fields; `configuration`
also retains T2R's existing first-constant installation. `standard` and
`dictionary` prove compatibility rather than asking for it. This is a selected
instance, not a claim that arbitrary free std dictionaries equal NP6. NP6's
full source-helper certificate supplies the scoped shipped unsafe/reference
interpretation; Lean slot specialization alone would give no native credit.
Allocator/ABI/SDK/extraction/hash/runtime and source-to-ELF boundaries remain.

**No frozen3 candidate or runtime persistence law is selected.** Interrupted
attempt015 had an extra guarded Rc2_History corollary; attempts018–020 remove
it from the selected result/top. The standalone development module is retained
as excluded work. CPS's unconditional source-event part remains; L094–L096 and
the L180 alias remain. No premise is erased merely by moving it into a record.
The new bank-model conclusions retain five explicit proof guards, counted below.
They do not gate inherited headline/finish outputs. No new T item is adopted.

### Totals per class and owner

“Actual antecedent” includes application guards inside advertised conditional
conclusions, as in Cons; it does not mean every such row is an outer root binder.
New bank guards are scoped separately in their row role. “Deployment alias” is
an umbrella, excluded from the deduplicated total. Counts are syntactic audit
families and do not measure a security percentage or independent proof gates.

| Scope | T | P | C | lead | session A | external |
|---|---:|---:|---:|---:|---:|---:|
'''
for scope,v in summary.items():text+='| '+scope+' | '+' | '.join(str(v['classes'].get(k,0)) for k in ['T','P','C'])+' | '+' | '.join(str(v['owners'].get(k,0)) for k in ['lead','session A','external'])+' |\n'
text+='\n| Scope / owner | T | P | C |\n|---|---:|---:|---:|\n'
for scope,v in summary.items():
 for owner,cs in v['by_owner'].items():text+='| '+scope+' / '+owner+' | '+' | '.join(str(cs.get(k,0)) for k in ['T','P','C'])+' |\n'
text+='''
Cons actual: 82T+174P. Eight Cons actual P families are removed by the checked
T2R composition; five CPR guard families are newly exposed, giving **82T+171P**.
If inspecting only inherited security conclusions, the five additional guards
do not apply: that slice is 82T+166P. L177 removes one deployment P family at
the selected Claims instance. No T/C change. L174 was ALREADY absent in Cons;
NP6 strengthens its same-run output, so there is no second subtraction. L179
is PARTIAL: Claims-local frame/ownership/cleanup is certified, whole-library/
native/runtime/artifact association is retained under that broader row.
L151–L153 remain structural model-carrier laws under the original universal
continuations; scoped instances are not a global source-arithmetic discharge.

### Pending OWNER routes and lead rows that can proceed

(a) Frozen3 adoption is an unadopted candidate replacement route for L157/L159;
L181/L182/L185 are the corresponding source/order/transport inventory and
aliases. Adoption alone is not claimed to close them. (b) Runtime law adoption
AND authoritative physical contract-game clarification gate L094–L096/L180;
ordinary-key eligibility, physical account identity, source action order and
final parent success cannot be hidden as experiment data. (c) Session A's
own rows remain pending; the additional lead-owned binding/source/model rows
explicitly tagged c consume their S1/S6 or S3/S4 interpretations. No live
session A worktree/candidate was touched. Tags describe the adopted work routes;
a different proof could replace a route without an OWNER decision.
'''
text+='\nLead P rows with NONE of a/b/c: **'+str(leadcounts['deduplicated'])+' deduplicated** ('+str(leadcounts['actual antecedent'])+' actual, '+str(leadcounts['deployment only'])+' non-alias deployment). All audit rows including aliases: '+str(len(lead))+'. IDs: '+', '.join(r['id'] for r in lead)+'.\n'
text+='''
This includes the two success-event restrictions and three structural carrier
rows: “can proceed” is not a claim that those are unproved independent gates.
Global artifact/replay/trust work is untagged because its own action can proceed
independently; final release use still depends on all unresolved source cones.

### Complete row diff against Cons_Top recount

| ID | Name | Class / owner | Status / scope | Exact correspondence or blocker |
|---|---|---|---|---|
'''
for d in diff:
 vals=[d['id'],d['name'],d['classification']+' / '+d['owner'],d['status']+' / '+d['scope'],d['reason']]
 text+='| '+' | '.join(str(v).replace('|','\\|').replace('\n',' ') for v in vals)+' |\n'
text+='''
### Every remaining P row, owner and exact blocker

Tags: a=frozen3 candidate adoption; b=runtime-law plus contract-game OWNER
clarification; c=session A rows/source interpretation; —=none of those routes.
All implication guards and existential witnesses retain their original joint
scope. New Rc2_P rows apply only to the added bank-model conclusions.

| ID | Scope | Owner | Law family | Exact blocker | OWNER route |
|---|---|---|---|---|---|
'''
for r in rows:
 if r['classification']!='P':continue
 vals=[r['id'],r['scope'],r['owner'],r['name'],r['blocker'],'; '.join(r['owner_waits']) or '—']
 text+='| '+' | '.join(str(v).replace('|','\\|').replace('\n',' ') for v in vals)+' |\n'
text+='''
### Validation and remaining boundary

22/60 Lean attempts including dependencies; zero dependency builds, 0/0 Kani.
Final top Rc2_019: exit0, 2.165615717s, 5328524KiB, swap0. Final statement/axiom
audit Rc2_022: exit0, 2.262392340s, 5303300KiB, swap0. Exact target/argv, source
revision/hash, dependency/tool hashes, limits, errors and full #print axioms
are retained per attempt. Six selected theorem audits use exactly
[propext, Classical.choice, Quot.sound]; excluded standalone History also had
standard-only axioms. Nine development failures (002/005/007/008/009/011/014/016/021)
remain excluded. No timeout, memory kill, unchanged failed-source/dependency replay,
cap/heartbeat increase, package replay or launcher/infrastructure edit.
Every compile uses -M7000 and a separate admitted scope with MemoryHigh6G,
MemoryMax8G, MemorySwapMax0, TasksMax64; at most one scope for this job.

Reused pinned coherent SInt2/T2R/Cons/NP6/PoolT/CPP/CPR/CPS dependencies and
NP6's source/Kani certificate; no new native proof or frozen dependency release
rebuild. No shipped/cfg(kani) file changed: the three-ELF rebuild trigger did
not fire. Inherited pins, not freshly reproduced: default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No wallet/key/account cleanup, release-scope change, foreign module change or
push. Next deliverables are the owner decisions above, same saved-Vec/Context
and source/model bindings, concrete primitive instances, then source/artifact
association and coherent release audit. The 100-bit target remains open.
'''
doc.write_text(original+text)
(OUT/'Rc2_LEDGER.md').write_text(text.lstrip())
print(json.dumps({'counts':summary,'lead_unblocked':leadcounts,'removed':list(removed),'new':result['newly_present']},indent=2))
