"""Additive evidence gates only. Never promotes a source cut into an emitted model."""
from pathlib import Path
import json,lzma,hashlib,copy,importlib.util,sys,re
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
J=lambda p:json.loads(p.read_text())
F='crates/aspis-core/src/field.rs::';W='crates/aspis-core/src/field/wide_exact.rs::'
SPECS=[('TX1:036',F+'qm31_accumulate_product_channels','NGA_Accumulate.source'),('TX1:044',F+'qm31_sum_products_small','NGA_SumAlgebra.source'),('TX1:040',F+'qm31_sum_products2','NGA_WrapperValues.two'),('TX1:041',F+'qm31_sum_products3','NGA_WrapperValues.three'),('TX1:043',F+'qm31_sum_products4','NGA_WrapperValues.four'),('TX1:056',W+'WideExact::square','NGA_WideSquare.source')]
STANDARD={'propext','Classical.choice','Quot.sound'}

def checked_claim(candidate):
 """New gates are conjunctions; a CLOSED callee or value theorem alone is insufficient."""
 assert candidate['row']in{r for r,_,_ in SPECS}
 assert candidate['native_valid']and candidate['same_input_domain_proved']
 assert candidate['emitted_association_valid'], 'Missing successful pinned emitted helper/cohort association'
 assert candidate['all_actual_callees_closed'], 'Actual selected callee remains OPEN'
 assert candidate['combined_scan_valid']and candidate['raw_ax2_standard']
 assert candidate['same_full_value_and_frame']
 assert candidate['trust_changes']==[], 'No new trust or metric change authorized'
 # Check historical facts themselves; caller-supplied True flags cannot launder them.
 rid=candidate['row']
 raw=lzma.open(R/'evidence/ledger7-20261104/NFX_LEDGER.json.xz').read()
 by={r['row']:r for r in json.loads(raw)['rows']}
 if rid in ['TX1:036','TX1:044']:
  assert any(J(p)['exit_status']==0 for p in E.glob('NGA_E???/receipt.json')), 'No successful emitted extraction exists in this job'
 elif rid in ['TX1:040','TX1:041','TX1:043']:
  assert by['TX1:044']['composed_status']=='CLOSED', 'Actual small helper remains OPEN'
 else:
  assert all(by[r]['composed_status']=='CLOSED'for r in ['TX1:032','TX2:022']), 'Actual QM31 square remains OPEN'
 return True

def proof_audit():
 review=E/'NGA_review';summary=J(review/'SUMMARY.json');assert summary['status']=='PASS'
 pin=J(E/'NGA_WALKER_PIN.json')
 assert sha(E/'NGA_WALKER_SOURCE.lean.txt')==pin['sha256']==sha(R/pin['original'])
 rows=summary['commands'];fixtures=next(x for x in rows if x['target']=='fixtures')['results']
 assert len(fixtures)==8 and all(x['equal']for x in fixtures)
 assert all(len(x['walked_axioms'])==1 for x in fixtures[:4])and all(not x['walked_axioms']for x in fixtures[4:])
 roots={}
 for row in rows:
  assert row['exit_status']==0 and int(row['swaps'])==0
  if row['target'].startswith('proof'):
   for x in row['results']:
    assert x['equal']and set(x['walked_axioms'])==set(x['collect_axioms'])<=STANDARD
    graph='NEP_'+row['target']+'_'+x['root']+'_REACHABLE.txt'
    data=lzma.open(E/(graph+'.xz')).read();assert hashlib.sha256(data).hexdigest()==(E/(graph+'.sha256')).read_text().split()[0]
    roots[x['root']]=dict(x,raw_graph=graph+'.xz',raw_graph_sha256=hashlib.sha256(data).hexdigest())
 assert set(roots)==set(J(E/'NGA_AUDIT_ROOTS.json')['roots'])
 scan=J(review/'SCAN_SUMMARY.json');assert scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
 # Every current proof source must be the actual input of a successful focused compile.
 attempts=[J(p)for p in E.glob('NGA_L???/receipt.json')]
 for module in J(E/'NGA_AUDIT_ROOTS.json')['modules']:
  source=E/(module+'.lean')
  assert any(r['exit_status']==0 and r['module']==module and sha(source)in r['source_hashes'].values()for r in attempts),module
 return roots,scan

def build():
 audited,scan=proof_audit()
 assert J(E/'NGA_NATIVE_REVALIDATION.json')['status']=='PASS'
 assert J(E/'NGA_NATIVE_NEW_RESULTS.json')['status']=='PASS_SUPPORT_ONLY'
 p=R/'evidence/ledger7-20261104/NFX_LEDGER.json.xz';raw=lzma.open(p).read();baseline_sha=hashlib.sha256(raw).hexdigest()
 assert baseline_sha==(p.with_suffix('.sha256')).read_text().strip()
 base=json.loads(raw);by={r['row']:r for r in base['rows']}
 # Retain the unchanged NFK admission semantics. No new candidate is eligible.
 path=R/'evidence/ledger6-20261104/NFK_validate.py';sp=importlib.util.spec_from_file_location('NGA_NFK',path);NFK=importlib.util.module_from_spec(sp);sp.loader.exec_module(NFK)
 out=NFK.admit(base,{}, {},{'NGA':[]})
 before={r['row']:r['composed_status']for r in base['rows']};after={r['row']:r['composed_status']for r in out['rows']};assert before==after
 pending=[];edges=[]
 for rid,fn,root in SPECS:
  assert by[rid]['function']==fn and by[rid]['composed_status']=='OPEN'
  square=rid=='TX1:056'
  reason=('Actual QM31::square callee OPEN at TX1:032/TX2:022 and outside Slice D. Per-callee emitted value laws and complete record/source equation do not supply that native bridge.'if square else
   'The required emitted generic helper/cohort association is absent. E001 and changed/split E002 both failed Aeneas InterpBorrows.ml:2731. All local typed-array, cache, frame, zero/arity/induction and field-value source-cut laws pass, but are not the missing emitted association.'if rid in ['TX1:036','TX1:044']else
   'Same-input wrapper and full field-value laws pass, but actual qm31_sum_products_small child remains OPEN on its emitted-helper/cohort association. No CLOSED child can be fabricated from the handwritten cut.')
  pending.append(dict(row=rid,function=fn,status='OPEN',support_root=root,raw_axioms=audited[root]['walked_axioms'],reason=reason))
  callee=(F+'QM31::square'if square else F+'qm31_accumulate_product_channels'if rid=='TX1:044'else F+'qm31_sum_products_small'if rid in ['TX1:040','TX1:041','TX1:043']else None)
  if callee:edges.append(dict(caller=fn,callee=callee,status='OPEN',support_root=root,reason=reason))
 def put(name,data):(E/name).write_text(json.dumps(data,indent=2)+'\n')
 put('NGA_CLOSED.json',dict(schema_version=1,frozen_revision=base['frozen_revision'],new_composed_functions=0,new_composed_rows=0,driver_root_status='OPEN',functions=[],open_candidates=pending))
 put('NGA_EDGES.json',edges)
 put('NGA_LEDGER_DELTA.json',dict(baseline=str(p.relative_to(R)),baseline_raw_sha256=baseline_sha,new_closed_rows=[],new_functions=0,no_other_status_change=True,validator_checks_added_only=True,unchanged_NFK_validator_sha256=sha(path),checks=['current source successful focused compile','same typed inputs and full output/frame','paired native/copy controls, frozen lock and features','successful actual emitted association required','every actual callee CLOSED required','headline combined raw ax2 and NFX scan','no new trust or metric change'],pending=pending))
 put('NGA_AUDIT.json',dict(status='PASS_SUPPORT_ONLY',roots=audited,raw_roots=len(audited),standard_axioms_only=True,scan=scan,walker_sha256=pinsha if (pinsha:=sha(E/'NGA_WALKER_SOURCE.lean.txt'))else None,fixtures=8,closure_credit=False,retained_trust=['P6/D188 option A reclassification','root physical ABI/borrows','compiler/library/Aeneas/source-to-ELF','RuntimePersistence','RuntimeReturnData accepted nonempty 1..1024','RuntimeMemcmp accepted','digest=H realization'],no_trust_or_metric_change=True))
 print(json.dumps(dict(valid=True,new_closed_rows=0,open_members=len(pending),raw_roots=len(audited),scan_modules=scan['modules'])))
if __name__=='__main__':build()
