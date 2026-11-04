"""Additive row gates over the repaired 599-row inventory; no baseline weakening."""
from pathlib import Path
import json,lzma,hashlib,importlib.util,sys,re,copy
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
J=lambda p:json.loads(p.read_text())
def module(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
N=module('NGH_native',E/'NGH_validate_native.py')
STANDARD={'propext','Classical.choice','Quot.sound'}
F='crates/aspis-core/src/field.rs::';W='crates/aspis-core/src/field/wide_exact.rs::'

def audit(review='NGH_review'):
 d=E/review;s=J(d/'SUMMARY.json');assert s['status']=='PASS'
 pin=J(E/'NGH_WALKER_PIN.json');assert sha(E/'NGH_WALKER_SOURCE.lean.txt')==pin['sha256']==sha(R/pin['original'])
 roots={};fixtures=[]
 for row in s['commands']:
  assert row['exit_status']==0 and int(row['swaps'])==0
  if row['target']=='fixtures':fixtures=row['results']
  if row['target'].startswith('proof'):
   for x in row['results']:
    assert x['equal']and set(x['walked_axioms'])==set(x['collect_axioms'])<=STANDARD
    name='NEP_'+row['target']+'_'+x['root']+'_REACHABLE.txt'
    raw=lzma.open(E/(name+'.xz')).read();assert hashlib.sha256(raw).hexdigest()==(E/(name+'.sha256')).read_text().split()[0]
    roots[x['root']]=x
 assert len(fixtures)==8 and all(x['equal']for x in fixtures)
 assert all(len(x['walked_axioms'])==1 for x in fixtures[:4])and all(not x['walked_axioms']for x in fixtures[4:])
 assert set(roots)==set(J(E/'NGH_AUDIT_ROOTS.json')['roots'])
 scan=J(d/'SCAN_SUMMARY.json');assert scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
 attempts=[J(p)for p in E.glob('NGH_L???/receipt.json')]
 for m in J(E/'NGH_AUDIT_ROOTS.json')['modules']+['NGH_COMBINED_IMPORT','NGH_Driver']:
  assert any(x['exit_status']==0 and x['module']==m and sha(E/(m+'.lean'))in x['source_hashes'].values()for x in attempts),m
 return dict(status='PASS',roots=roots,standard_axioms_only=True,scan=scan,fixtures=8,walker_sha256=pin['sha256'],review=review,cold_release_replay=False)

def helper_gate(candidate):
 assert candidate['row']in ['TX1:036','TX1:044','TX1:040','TX1:041','TX1:043']
 # Even all-True caller flags cannot manufacture the required actual-helper contract.
 raise AssertionError('No admitted proof_for_contract of the ACTUAL frozen generic helper; one-step support is not that contract. Ruling-(ah) status remains OPEN.')

def build(stage='square',review='NGH_review'):
 assert stage in ['square','wide'];N.build();a=audit(review)
 assert J(E/'NGH_SOURCE_ASSOCIATION.json')['status']=='PASS'
 p=R/'evidence/inv-repair-20261104/NGB_ADMITTED_LEDGER.json.xz';raw=lzma.open(p).read();rawsha=hashlib.sha256(raw).hexdigest();assert rawsha==p.with_suffix('.sha256').read_text().strip()
 base=json.loads(raw);assert len(base['rows'])==599
 vpath=R/'evidence/ledger6-20261104/NFK_validate.py';V=module('NGH_NFK',vpath);V.BASE_CREDITS=base['NEZ_credits']
 nfbase=json.loads(lzma.open(R/'evidence/ledger7-20261104/NFX_LEDGER.json.xz').read())
 unchanged=V.admit(nfbase,{}, {},{'NGH':[]});original={r['row']:r['composed_status']for r in nfbase['rows']};assert original=={r['row']:r['composed_status']for r in unchanged['rows']}
 before={r['row']:r['composed_status']for r in base['rows']};assert all(before[r]==s for r,s in original.items())
 by={r['row']:r for r in base['rows']}
 for rid in ['TX1:001','TX1:002','TX1:007','TX1:035','TX2:001','TX2:002','TX2:004','TX2:025']:assert by[rid]['composed_status']=='CLOSED'
 nft=J(E.parent/'slice-d-field-20261104/NFT_CLOSED.json');cm=next(x for x in nft['functions']if x['function']==F+'CM31::square');assert cm['status']=='CLOSED'and cm['native_positive']=='NFT_K020'and cm['matched_control']=='NFT_K021'
 ids=['TX1:032','TX2:022'];root='NGH_QSquareOps.source';assert root in a['roots']
 closed=[dict(function=F+'QM31::square',rows=ids,status='CLOSED',form='ordinary ruling (y), local-record opaque products; slice-Q boundary authorized in NGH job',domain='same canonical four-limb receiver',native_positive='NGH_K011',matched_control='NGH_K012',argument_control='NGH_K013',copy_pair=['NGH_K014','NGH_K015'],lean_root=root,emitted_association='NGH_QSquareRef.model_eq',stub_laws=['NGH_CMWords.square','NGH_CMWords.product'],domain_proof='NGH_QSquareOps.source derives both same canonical component inputs and all three canonical replies, then substitutes their actual emitted totality/value laws.',frame='full returned record; no input writes or security-relevant effects',trust='P6/D188 option A reclassification; no trust removed or added')]
 edges=[dict(caller=F+'QM31::square',callee=F+name,status='CLOSED',selected=True,domain_proof='NGH_QSquareOps.source and NGH_CMWords; same canonical arguments and derived replies',native='NGH_K011',control='NGH_K012')for name in ['CM31::square','CM31::mul','CM31::add','CM31::double','mul_by_r']]
 if stage=='wide':
  assert 'NGH_WideBridge.source'in a['roots'];ids+=['TX1:056']
  for rid in ['TX1:024','TX1:029','TX1:061']:assert by[rid]['composed_status']=='CLOSED'
  closed.append(dict(function=W+'WideExact::square',rows=['TX1:056'],status='CLOSED',form='ordinary ruling (y), inherited validated local-record native caller plus newly CLOSED QM31 square',domain='same canonical eight-limb receiver',native_positive='NFT_K098',matched_control='NFT_K099',argument_control='NFT_K100',lean_root='NGH_WideBridge.source',model_substitution='NGH_WideBridge.same_square',domain_proof='NGA_WideSquare.value/source derives canonical c0,c1, bb and u; NGH_QSquareOps.source is substituted on each actual c0/c1.',frame='full returned record; no input writes or security-relevant effects',trust='retained P6/D188 option A; no additional trust'))
  edges += [dict(caller=W+'WideExact::square',callee=F+'QM31::square',status='CLOSED',selected=True,domain_proof='NGA_WideSquare.value, NGH_WideBridge.same_square',callee_rows=['TX1:032','TX2:022'])]
  edges += [dict(caller=W+'WideExact::square',callee=callee,status='CLOSED',selected=True,domain_proof='NGA_WideSquare.value derives same canonical operands and intermediate bb; NGH_WideBridge.source composes the actual operations',native='NFT_K098',control='NFT_K099',argument_control='NFT_K100')for callee in [F+'QM31::mul',F+'QM31::add',W+'mul_u']]
 for rid in ids:assert by[rid]['composed_status']=='OPEN'
 openids=['TX1:036','TX1:044','TX1:040','TX1:041','TX1:043']
 pending=[dict(row=r,function=by[r]['function'],status='OPEN',reason='Actual helper-level contract missing; checked one-step contract/reference transcription/Lean induction remain support. Do not promote under (ah) without that gate or a lead clarification.')for r in openids]
 out=copy.deepcopy(base)
 for r in out['rows']:
  if r['row']in ids:r['composed_status']='CLOSED'
 assert {r['row']:r['composed_status']for r in out['rows']if r['row']not in ids}=={r:s for r,s in before.items()if r not in ids}
 def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
 put('NGH_AUDIT.json',a);put('NGH_CLOSED.json',dict(schema_version=1,frozen_revision=base['frozen_revision'],new_composed_functions=len(closed),new_composed_rows=len(ids),driver_root_status='OPEN',functions=closed,open_candidates=pending))
 put('NGH_EDGES.json',edges)
 put('NGH_LEDGER_DELTA.json',dict(baseline=str(p.relative_to(R)),baseline_raw_sha256=rawsha,inventory_rows=599,new_closed_rows=ids,new_functions=len(closed),no_other_status_change=True,validator_checks_added_only=True,unchanged_NFK_validator_sha256=sha(vpath),prior_deltas_preserved_not_rebooked=['NFT','NFU','NFS','NFY'],ruling_ah_rows=[],prerequisite_prior_rows=[dict(row='TX1:011',packet='evidence/slice-d-field-20261104/NFT_CLOSED.json',function=F+'CM31::square',revalidated_pair=['NFT_K020','NFT_K021'],rebooked=False)],pending=pending,checks=['native result and argument controls','exact KMX plus failing same-shape copy control','frozen offline dependency graph before every run and unchanged lock after','every actual callee CLOSED and domain proved','actual emitted model association for square','current source successful focused Lean compile','headline combined import, byte-identical ax2 walker, eight fixtures, zero-defect NFX scan','unchanged NFK base admission and no unrelated status changes']))
 print(json.dumps(dict(valid=True,new_closed_rows=ids,raw_roots=len(a['roots']),scan_modules=a['scan']['modules'])))
if __name__=='__main__':build(*sys.argv[1:])
