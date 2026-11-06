"""Read-only candidate review against the authoritative NKC statements and obligations."""
from pathlib import Path
import json,lzma,hashlib,copy,re
E=Path(__file__).resolve().parent;P=E.parent/'ledger17-20261108';H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def put(n,x):
 raw=(json.dumps(x,indent=1)+'\n').encode();p=E/n
 if n.endswith('.xz'):p.write_bytes(lzma.compress(raw));Path(str(p)[:-3]+'.sha256').write_text(H(raw)+'\n')
 else:p.write_bytes(raw)
b=J(P/'NKC_LEDGER.json.xz');by={r['row']:r for r in b['rows']};statements={}
q=E/'NKH_L002/stdout.log'
for l in (q.read_text()if q.exists()else lzma.decompress(Path(str(q)+'.xz').read_bytes()).decode()).splitlines():
 if 'NKH_OWNER 'in l:
  x=json.loads(l.split('NKH_OWNER ',1)[1]);assert x['root']not in statements;statements[x['root']]=x

extra_statements=E/'NKH_EXTRA_STATEMENTS.json'
if extra_statements.exists(): statements.update(J(extra_statements))
missing_roots=sorted(set(J(E/'NKH_AUDIT_ROOTS.json')['roots'])-set(statements))
assert missing_roots==['NJJ_Value.projection','NJR_WeightFailure.weights']
assert len(statements)==10064
old=J(P/'NKC_KERNEL_STATEMENTS.json.xz');wrong=[r for r in old if old[r]!=statements.get(r)];assert not wrong,wrong[:5]
put('NKH_KERNEL_STATEMENTS.json.xz',statements);put('NKH_OWNER_COMPARISON.json',dict(status='PASS',predecessor_roots=len(old),identical=len(old),new_roots=len(statements)-len(old),mismatches=wrong))
# Compare all original clauses, rather than candidate deltas from older ledgers.
rows=[]
for folder,pre in J(E/'NKH_SPECS.json')[1:4]:
 e=E.parent/folder
 baseline=J(e/'NJZ_BASELINE_ROWS.json')if pre=='NJZ'else None
 if baseline is None:baseline=J((E/'NKH_NJX_BASELINE.json.xz')if pre=='NJX'else P/'NKC_LEDGER.json.xz')['rows']
 for f in J(e/f'{pre}_CLOSED.json')['functions']:
  for rid in f['rows']:
   r=by[rid];assert r['status']=='OPEN'and r['function']==f['function']and r['frozen_body_sha256']==f['frozen_body_sha256'],rid
   if f.get('baseline_obligation_statement_hash'):assert f['baseline_obligation_statement_hash']==r['obligation_statement_hash']
   original=next(v for v in baseline if v['row']==rid)
   assert original['obligation_statement_hash']==r['obligation_statement_hash'],(rid,'hash')
   assert original['obligation']==r['obligation'],(rid,'complete obligation')
   ks=[statements[n]for n in f['lean_roots']if n in statements]
   missing=[n for n in f['lean_roots']if n not in statements]
   specific={
    'NJZ':'Complete source-site Reservation/typed inputs and exact per-step native cuts. Reader native specialization ONLY N4/16/32, backing1768, bounded cursor; broader kernel equalities receive no broader native credit. echeck (ah)/(ay) error/record/step coverage in NKH_COVERAGE.json.',
    'NKD':'Canonical digits/amount or arbitrary32-byte sample input; exact source-step cuts. Transcript ONLY deployed SolanaDigest, row<=95/payload<=8192; hashv is the unchanged runtime reply realization, not a generic-hasher native theorem. Actual child domains follow SAME low/add/decode trace.',
    'NJX':'Only SAME canonical lambda/high/opened16; expected digest bounds only on entered arm. Source/reference full field replies/cache/frames/ordered traces are conclusions. NJL child roots retained CLOSED in NKC at identical arguments, checked in NKH_NJL_REVIEW.json.'}[pre]
   cls={k:copy.deepcopy(r['obligation'][k])for k in['named_hypotheses','inventory_domain_obligations','caller_domain_obligations']}
   rows.append(dict(row=rid,provider=pre,function=r['function'],basis_obligation_statement_hash=r['obligation_statement_hash'],frozen_body_sha256=r['frozen_body_sha256'],certificate=f,root_domain=f['root_domain'],roots=f['lean_roots'],primary_root=f['lean_roots'][0],original_clauses=cls,kernel_statements=ks,checks=dict(basis_function_body_and_complete_obligation=True,no_double_count=True),clause_review=[dict(original=c,proof_roots=f['lean_roots'],disposition='Retained verbatim; SAME actual call/full Result/error/abort/frame/ordered effects composed in listed roots; caller-owned context remains explicit at parent.')for c in cls['caller_domain_obligations']],hypothesis_inventory=dict(allowed_ruling='(aq)(2)',ordinary_inputs=f['root_domain'],reviewed_native_cuts='Exact per-step/source-fragment cuts, retained P6/D188 option-A transport',source_site_reservation='Universal actual-site Reservation where present; never success-only',added_game_hypotheses=[],no_arbitrary_Ops_Run_endpoint_or_child_success_premise=True,complete_kernel_statements=[k['root']for k in ks]),admissible_pending_gate=False,missing_kernel_roots=missing,admission_blocker="Full all-root gate incomplete after host ENOSPC; no credit",review=specific))
assert len(rows)==len({r['row']for r in rows})==28
cs={x['row']:x for x in rows};parents=[]
for c in rows:
 r=by[c['row']]
 for par in b['rows']:
  if par['transaction']!=r['transaction']or r['function']not in par['canonical_callees']:continue
  if par['row']=='TX1:069'and c['row']=='TX1:202':continue  # (az)(1): edge retained, not an actual call
  internal=par['row']in cs
  for kind,required in [('own',c['root_domain'])]+[('inventory:'+o['unit'],o['domain'])for o in r['obligation']['inventory_domain_obligations']]:
   roots=cs[par['row']]['roots']if internal and kind=='own'else None
   clause=dict(id=f'NKH-caller:{par["row"]}:{c["row"]}:{kind}',caller=par['function'],callee=r['function'],required=required,status='DISCHARGED'if roots else'OPEN',discharged_by=roots,reason='SAME internal call domain derived by named composed roots.'if roots else'Incoming unit/provenance belongs to parent; helper closure does not close parent.')
   parents.append(dict(parent=par['row'],helper=c['row'],kind=kind,caller_clause=clause,parent_candidate=internal))
put('NKH_CANDIDATE_REVIEW.json',dict(status='NOT_ADMITTED_HOST_DISK_FULL_GATE_INCOMPLETE',rows=rows,no_double_count=True,comparison_basis='NKC, all28 independently OPEN; no ledger15 delta reused'))
put('NKH_PARENT_CLAUSES.json',dict(clauses=parents,parents=sorted({x['parent']for x in parents}),no_unsubmitted_parent_promotion=True,excluded_spurious_parent_edge=dict(caller='TX1:069',callee='TX1:202',ruling='(az)(1)',reason='Derived QueryScan default; graph edge retained, no actual IncrementalMerkleTree call/domain clause')))
# Every NJL row-level child of a submitted NJX row remains CLOSED in NKC;
# source helper uses are at lambda/o/powers/cache/high actually constructed there.
children=[]
for c in rows:
 if c['provider']!='NJX':continue
 for f in by[c['row']]['canonical_callees']:
  r=next((r for r in b['rows']if r['transaction']=='TX1'and r['function']==f),None)
  if r and any(x['owner_module'].startswith('NJL_')for x in r.get('root_owners',[])):
   assert r['status']=='CLOSED'
   for owner in r['root_owners']:assert statements[owner['root']]==old[owner['root']]
   children.append(dict(parent=c['row'],child=r['row'],function=f,status='CLOSED_IN_NKC',roots=r['root_owners'],same_arguments='Actual SAME canonical inputs; internally constructed power/cache packet and expected digest, no independently selected reply'))

helper_names=['AspisR1.NJL_WindowPowerArray.source','AspisR1.NJL_WindowFold.source','AspisR1.NJL_Traverse.packet','AspisR1.NJL_CachedPowers.source','AspisR1.NJL_CacheReads.canonical']
for n in helper_names:assert statements[n]==old[n],n
put('NKH_NJL_REVIEW.json',dict(status='PASS',row_children=children,unchanged_NKC_helper_roots=[statements[n]for n in helper_names],no_direct_NJL_row_child_in_submitted_canonical_edges=(not children),helper_sources=['NJX_WindowInvocation.source: NJL_WindowPowerArray.source lambda hl; NJL_WindowFold.source SAME power/cache/o/start and constructor laws','NJX_DigestResiduals.source: NJL_Traverse.packet on SAME expected/opened/high'],new_credit=0))
(E/'NKH_HYPOTHESIS_INVENTORY.md').write_text('# NKH hypothesis inventory\n\nComplete kernel statements and canonical owners: NKH_KERNEL_STATEMENTS.json.xz; each original clause is retained in NKH_CANDIDATE_REVIEW.json. Reviewed native cuts are explicit under(aq)(2), option-A P6/D188 RECLASSIFICATION; no new game assumption or arbitrary operation dictionary.\n\n'+''.join(f'- {r["row"]}: {r["hypothesis_inventory"]}. {r["review"]}\n\n'for r in rows))
print(json.dumps(dict(stage='review',candidates=len(rows),parent_clauses=len(parents),njl_row_children=len(children),predecessor_roots_unchanged=len(old))))
