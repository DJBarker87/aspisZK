"""Render the statement-reviewed dispositions. No prover or implementation edits."""
from pathlib import Path
import json,re,copy
from collections import Counter
P=Path(__file__).resolve().parent;OUT=P.parent
base=json.loads((OUT/'rows.json').read_text());rows=copy.deepcopy(base);by={r['id']:r for r in rows}
checks=json.loads((P/'checks.json').read_text())
for r in rows:
 r['recount1_status']=r.pop('recount_status');r['recount2_status']=r['recount1_status'];r['recount1_bucket']=r.get('dependency_bucket')
 r['recount2_basis']='Re-read original statement and retained residual/model scope. Research-present defining sources are unchanged except LOG; candidate-only definitions are resolved to pinned git objects in resolved-definitions.json. Original model/guard/overlap/trust scope remains supported; no installed label alone is credited.'
 r['recount2_evidence']=['recount2/definition-audit.json','recount2/resolved-definitions.json',r['audit_evidence']]
def change(key,status,why,fields=None,ev=None,theorem=None,bucket=None):
 r=by[key];r['recount2_status']=status;r['recount2_basis']=why
 if fields is not None:r['residual_fields']=fields
 if theorem is not None:r['theorem']=theorem
 if ev:r['recount2_evidence']=ev
 r['dependency_bucket']=bucket if status=='OPEN' else None
# Every newly committed extracted-source equation is counted once at its callback scope.
for i,c in enumerate(checks[:8]):
 for module,theorem in c['items']:
  op=int(re.search(r'op(\d+)_source',theorem)[1]);r=next(r for r in rows if r.get('group')=='O' and re.match(r'op'+str(op)+r'\b',r['name']))
  change(r['id'],'CLOSED-ON-CANDIDATE','Complete selected callback = literal extracted source Result equation, arbitrary input/traits/dictionary; no desired-output premise. D188 extraction boundary. Native world/cost/erasure/Drop composition stays V165/V167, not a second condition on this source-value row.',[],[f'recount2/out-{24300+i}.log','recount2/manifest.json'],theorem)
for key,op in [('V200',78),('V248',231)]:
 change(key,'CLOSED-ON-CANDIDATE','Exact extracted fibre/clone body is selected at the simultaneous dictionary, with full Result and arbitrary field traits; no success equation assumed. Earlier broader native adequacy residual is separately V165/V167. Installed label alone was not used.',[],['recount2/out-24308.log','recount2/dict/docs/research/v8-r0-zk-20261009/lean/R1Z/PDict_RemainingDictionary231.lean.txt'],f'R1Z.PDict_RemainingDictionary231.op{op}_installed')
for key,theorem in [('V255','R1Z.PV_TraceValueInstall.source'),('V262','R1Z.PV_ProverRwP7CoefficientsInstall.source')]:
 change(key,'CLOSED-ON-CANDIDATE','Complete cfg-selected extracted source callback supplied and consumed through the caller; all Variant cases for op255, selected ct-host-prover value body for op247. Native feature/world association remains V166/V167. D207 supported at exact source-row scope.',[],['recount2/out-24312.log','recount2/rw/docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p8/README.md'],theorem)
# Respect the requested REDUCED disposition for the eight-field endpoint record.
# No concrete Runtime/Boundary is supplied and no field is treated as discharged.
fields={'V038':['disclosed_V038','observerOracle_V038'],'V045':['source_V045'],'V336':['native_fill_V336'],'V337':['native_ledger_V337'],'V338':['byte_blind_V338'],'V339':['kernels_V339']}
for key,fs in fields.items():
 change(key,'REDUCED','D205: conditional endpoint over free runtime and boundary; named obligations exposed, zero whole deployed rows discharged. This REDUCED bookkeeping credit does not assert a concrete runtime, availability, E1/E2, agreement, or native instance. All listed fields and concrete-instance association remain.', ['R1Z.PV_RunJoin_Endpoint.PV_RunJoin_Premises.'+f for f in fs]+['R1Z.PV_RunJoin_Deployed.Runtime: frozen extracted-client instance missing','R1Z.PV_RunJoin_Boundary.Data: native instance missing'],['recount2/runjoin/docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_Endpoint.lean.txt','LOG D205; D206','recount2/receipts.json'])
for key in ['V036','V037']:
 change(key,'OPEN','Both marginals are theorems on the abstract graph coupling; complete row asks for SAME actual deployed coupling. Free Runtime/Boundary still uninstantiated. uniform_V037 is not a deployed marginal certificate; shared-host Endpoint object is older and fresh helper 24309 rejected that name.', ['PV_RunJoin_WorldCoupling.cp runtime.meanR' if key=='V036' else 'PV_RunJoin_Endpoint.uniform_V037; PV_RunJoin_WorldCoupling.cp runtime.meanM','frozen Runtime/Boundary instance'],['recount2/runjoin/docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_Endpoint.lean.txt','recount2/out-24309.log'],bucket='b')
for key,part in [('V152','public_eq'),('V153','build_eq'),('V154','transport_eq')]:
 change(key,'OPEN','Extracted public/bank/transport stages and canonical encoding have checked identification/BuilderPremises consumers. Complete actual returned-compiler identification and deployed carrier association are not supplied: NativeIdentification/ForestCompilation remain prepared in pinned handoff. Canonical encoding and generic premises do not close whole actual-source row.', ['PV_Src_Identification.PV_Src_Premises.words','PV_Src_Identification.PV_Src_Premises.publicCorr','PV_Src_Identification.PV_Src_Premises.admission','PV_Src_Identification.PV_Src_Premises.row_call','PV_Src_NativeIdentification.PV_Src_Premises.compile_call (native composition pending)'],['recount2/out-24311.log','recount2/srcid/evidence/pv-srcid-20261026/HANDOFF.md','recount2/srcid/docs/research/v8-r0-zk-20261009/lean/R1Z/PV_Src_Canonical.lean.txt'],bucket='a')
for key in ['V221','V222','V249','V263','V267']:
 change(key,'OPEN','Actual volatile erasure/fence, Instant time, worker scheduling/panic, or filesystem write/partial-error world law requires the effect-aware interpreter; a value law or sibling reuse cannot supply it. Reclassify from independent to native dependency using actual emitted callback statement.',None,['recount2/cb/evidence/pv-cb-20261026/FINAL-STATUS.md','recount2/cb/evidence/pv-cb-20261026/ENTRIES.md'],bucket='b')
change('V269','OPEN','Type27 is Formatter, not fallible-store transport. PDict_FallibleTransport/StoreTransport source equations do not supply reachable Debug/Display sink bytes/options/failure/state interpretation. D203 REDUCED claim is unsupported for this whole row; native type count remains26/28.', ['native Formatter type27/sink/world association'],['recount2/dict/docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/lift222/HANDOFF.md','recount2/dict/docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/quotient231/TYPES.md'],bucket='b')
for key in ['V340','V346','V397','V398','V399']:
 by[key]['recount2_basis']='Rebase artifact/fixture/differential gates are measured, but proof/source/native/candidate association and coherent final replay are absent. Latest research Rust content equals measured control. Matching finite artifacts does not rebind universal proofs or complete release dependency closure.'
 by[key]['recount2_evidence']=['recount2/rebase/design/PV-REBASE-20261026.md','recount2/receipts.json']
for key in ['V341','V342','V343','V372','V344','V345','V370','V371','V373','V374','V396','V380-inversion']:
 by[key]['recount2_evidence'] += ['recount2/rebase/design/PV-REBASE-20261026.md' if key in ['V341','V342','V343','V344','V345'] else 'recount2/l3/design/PV-L3-20261026.md']
for key in ['V344','V345','V374']:
 by[key]['recount2_basis']='No qualified timing gate completed. Owner quiet-host/Docker-cap scheduling barrier remains; no permission to bypass it. Invalidated sample/queue retained, no median or successful dudect gate inferred.'
# Newly explicit obligations, never renumber original V380 or its inversion alias.
def add(key,name,cls,status,why,ev,bucket=None,fields=[]):
 r=dict(id=key,name=name,classification=cls,group='NEW',recount1_status='NOT-PREVIOUSLY-SEPARATE',recount2_status=status,recount1_bucket=None,dependency_bucket=bucket,residual_fields=fields,theorem=None,recount2_basis=why,recount2_evidence=ev,meaning=name);rows.append(r);by[key]=r
add('V400','OS entropy failure / D206 model coverage repair (C/T-suspect)','C','OPEN','Selected OS EIO fault yields a pre-body error with empty oracle log. Conditional disagreement and first-draw witness independence have explicit runtime/fault/decoder/model-success hypotheses; no concrete outside-bad witness or privacy attack. Owner must choose A OsAvailable trust or B public failure in both experiments; neither adopted. Native association remains secondary. Do not invent new trust before adoption.', ['LOG D206','recount2/runjoin/docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_OsFailure.lean.txt','recount2/runjoin/evidence/pv-runjoin-20261026/concrete-attempt/receipt-23434.json'],bucket='c',fields=['owner model repair A/B','concrete runtime/fault/decoder association; outside-bad coordinate witness'])
add('V401','Fixed-coin rebase fixture byte equality','P','EVIDENCED','Both transfer/withdrawal complete proof/public bytes, status/attempt/callback/audit equal on pinned control/candidate. Separate measurement deliverable missing from original rows; overlaps V340/V399, not another universal source proof.', ['recount2/rebase/docs/research/100bit-spend-path-20261013/evidence/pv-rebase-20261026/fixture-comparison.json'],fields=['V340 proof rebind; V399 final release association'])
add('V402','Corrected 1000-pair rebase differential','P','EVIDENCED','Corrected capacity-checked cohort1000/1000;600 success pairs,100 rejected-prefix pairs,400 error tapes (prefix category overlaps success); four full oracle-stream pairs. v2 pressure-induced mismatch is invalidated and retained, not erased. Finite evidence only; no universal trace/refinement.', ['recount2/rebase/docs/research/100bit-spend-path-20261013/evidence/pv-rebase-20261026/corpus-v3/pipeline-final.json','recount2/rebase/design/PV-REBASE-20261026.md'],fields=['V340/V346/V399 universal proof/release association'])
def count(rs):return dict(rows=len(rs),classes=dict(Counter(r['classification'] for r in rs)),statuses=dict(Counter(r['recount2_status'] for r in rs)),open_dependencies=dict(Counter(r['dependency_bucket'] for r in rs if r['recount2_status']=='OPEN')))
summary={'recount1':json.loads((OUT/'totals.json').read_text())['recount_with_inversion'],'recount2_same400':count(rows[:400]),'recount2_all':count(rows),'lean_invocations':15,'kani_invocations':0,'premises_removed':0,'premises_added':0,'premises_weakened':0}
(P/'rows2.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n');(P/'totals2.json').write_text(json.dumps(summary,indent=2)+'\n')
lines=['# Recount 2 2026-10-26 (B): every row','','All400 inherited statements were re-read against the current research defining sources and pinned candidate statements. New rowsV400–V402 are explicit below. REDUCED retains every named obligation; no candidate is adopted. `a` independent; `b` actual extracted deployed caller interpretation; `c` owner decision (owner-first). See recount2/METHOD2.md for scope, corrections, and receipts.','','|Row / class|Recount1 → recount2|OPEN bucket|Statement basis and exact residual / theorem|Evidence|','|---|---|---|---|---|']
for r in rows:
 detail='; '.join(([r['theorem']] if r.get('theorem') else [])+r['residual_fields'])+'. '+r['recount2_basis']
 lines.append('|'+r['id']+' / '+r['classification']+'|'+r['recount1_status']+' → '+r['recount2_status']+'|'+(r['dependency_bucket'] or '—')+'|'+detail.replace('|','\\|')+'|'+'; '.join(r['recount2_evidence'])+'|')
(OUT/'ROWS2.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(summary,indent=2))
