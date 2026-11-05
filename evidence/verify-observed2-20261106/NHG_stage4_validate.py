"""Add native loop/caller associations without weakening historical admission."""
from pathlib import Path
import json,hashlib,subprocess,lzma,copy,importlib.util,re,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(n):return json.loads((E/n).read_text())
def historical(n):return subprocess.check_output(['git','show',read('NHG_STAGE3_SEAL.json')['revision']+':'+str((E/n).relative_to(R))],cwd=R)
spec=importlib.util.spec_from_file_location('NHG_v3',E/'NHG_stage3_validate.py');v3=importlib.util.module_from_spec(spec);spec.loader.exec_module(v3)
requirements={
'TX1:132':('AspisR1.NHG_FinishLeaves.boundary_result',[49],[50],['TX1:024']),
'TX1:135':('AspisR1.NHG_FinishLeaves.value_result',[51],[52],['TX1:024','TX1:029']),
'TX1:259':('AspisR1.NHG_SelectedClaim.returned',[53],[54],[]),
'TX1:236':('AspisR1.NHG_ExtraLeaves.carry_result',[57],[58],[]),
'TX1:239':('AspisR1.NHG_ExtraLeaves.empty_source',[59],[60],[]),
'TX1:258':('AspisR1.NHG_ExtraLeaves.scalar_source',[55],[56],['TX1:024']),
'TX1:241':('AspisR1.NHG_ExtraLeaves.initial_source',[63],[64],['TX1:024']),
'TX1:257':('AspisR1.NHG_ExtraLeaves.reconstruct_result',[61,73],[62,74],['TX1:024']),
'TX1:262':('AspisR1.NHG_ExtraLeaves.sum_result',[65,71],[66,72],['TX1:024']),
'TX1:240':('AspisR1.NHG_ExtraLeaves.equality_result',[67,69,75],[68,70,76],['TX1:024','TX1:029','TX1:033'])}
def validate(candidate='NHG_CLOSED.json'):
 seal=read('NHG_STAGE3_SEAL.json');assert seal['revision'].startswith('ed0fb939429')
 for n,p in seal['files'].items():
  b=historical(n);assert sha(b)==p['sha256']and len(b)==p['bytes']
 assert(E/'NHG_stage3_validate.py').read_bytes()==historical('NHG_stage3_validate.py')
 prior=json.loads(historical('NHG_CLOSED.json'));assert len(prior['functions'])==8
 assert json.loads(historical('NHG_STAGE3_VALIDATION.json'))['status']=='PASS'
 controls=json.loads(historical('NHG_STAGE3_MUTATIONS.json'));assert len(controls)==16 and all(x['rejected']for x in controls)
 closed=read(candidate);assert closed['functions'][:8]==prior['functions'];new=closed['functions'][8:];assert {f['rows'][0]for f in new}==set(requirements)
 for a,b in [(49,50),(51,52),(53,54),(55,56),(57,58),(59,60),(61,62),(63,64),(65,66),(67,68),(69,70),(71,72),(73,74),(75,76)]:v3.native(f'NHG_K{a:03}',f'NHG_K{b:03}')
 # The product oracles never call an actual field multiplication.
 semantic=(E/'NHG_K051/sources/NHG_src/crates/aspis-r1-cost-probe/src/NHG_semantic_steps.rs').read_text();assert 'product_cut(acc,alpha[round],&mut log)'in semantic and '.mul('not in semantic
 equality=(E/'NHG_K069/sources/NHG_src/crates/aspis-statement/src/pool_v1/NHG_semantic.rs').read_text();start=equality.index('fn NHG_equality_step()');assert 'mul_log(product,factor,&mut log)'in equality[start:] and '.mul('not in equality[start:]
 assert 'assert_eq!(iter.len(),next)'in semantic and 'kani::assume(index>0)'in semantic
 assert 'kani::assume(index<28)'in semantic
 for module,n in {'NHG_FinishLeaves':70,'NHG_SelectedClaim':72,'NHG_AddWords':76,'NHG_ExtraLeaves':80,'NHG_COMBINED_IMPORT':81}.items():
  rc=read(f'NHG_L{n:03}/receipt.json');assert rc['exit_status']==0 and sha((E/(module+'.lean')).read_bytes())==rc['source_hashes']['NHG_generated/'+module+'.lean']
  assert all('sorryAx'not in x for x in rc['print_axioms'])
 roots=read('NHG_STAGE4_ROOTS.json');walked=[]
 for i in roots['batches']:
  raw=read(f'NHG_audit/batch{i}/proof{i}.json');assert raw['exit_status']==0;walked+=raw['results']
 assert set(roots['roots'])=={x['root']for x in walked}and len(walked)==26
 assert all(x['equal']and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for x in walked)
 for n in range(81,86):assert read(f'NHG_L{n:03}/receipt.json')['exit_status']==0
 scan=list(map(json.loads,(E/'NHG_LOADED_scan.jsonl').read_text().splitlines()));assert len(scan)>=13541 and all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
 constants=read('NHG_CONSTANT_PINS.json');assert constants['cells']==168 and constants['byte_values_equal']is True
 rust=subprocess.check_output(['git','show',constants['native_revision']+':'+constants['native_path']],cwd=R);assert sha(rust)==constants['native_sha256']
 model=(R/constants['model_path']).read_bytes();assert sha(model)==constants['model_sha256']
 vals=list(map(int,re.findall(rb'\b\d+\b',rust.split(b'= [',1)[1].split(b'];',1)[0])))
 a=model.index(b'def pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1');b=model.index(b'/--',a);assert vals==list(map(int,re.findall(rb'(\d+)#u32',model[a:b])))and len(vals)==168
 resolutions=read('NHG_STAGE4_RESOLUTIONS.json');assert set(resolutions)==set(requirements)
 allroots={r for g in read('NHG_AUDIT_ROOTS.json')['groups']for r in g}
 for f in new:
  row=f['rows'][0];root,p,c,edges=requirements[row];assert f['status']=='CLOSED'and f['lean_root']==root and f['internal_edges']==edges and f['inner_hypotheses_remaining']==[]
  assert f['native_positive']==[f'NHG_K{n:03}'for n in p]and f['matched_control']==[f'NHG_K{n:03}'for n in c]
  assert all(r in allroots for key in ['domain_roots','carrier_roots','ordered_effect_roots']for r in f.get(key,[]))and root in allroots
  assert f['KMX_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  assert 'RECLASSIFICATION'in f['trust']and'retained'in f['trust']and f['native_field_multiplication']is False
  assert f['source_transport']=='ruling (y); one native iteration/window or full small function, retained emitter equality/induction, exact same operands and full Result'
  assert resolutions[row]['actual_edges']==edges
  tokens={'TX1:132':['Canonical polynomial28','coefficient0 is added twice'],'TX1:135':['all alpha10','round<10'],'TX1:259':['point<3,column<28','No canonicality'],'TX1:236':['Every U64','carry<=20'],'TX1:239':['level<21','168'],'TX1:258':['unrestricted','canonical'],'TX1:241':['canonical','four-component'],'TX1:257':['All16','index0..9'],'TX1:262':['low16','length<=2','end<=64'],'TX1:240':['arrays10 canonical','index1..10']}
  assert all(token in f['domain'] for token in tokens[row])
  if row=='TX1:135':assert f['paired_product_laws']==['AspisR1.NHG_Product.words','AspisR1.NHG_FinishLeaves.product_packet','AspisR1.NHG_FinishLeaves.value_packet_step']
  if row=='TX1:240':assert f['paired_product_laws']==['AspisR1.NHG_AddWords.nq_mul']
 baseline_path=R/'evidence/ledger9-20261105/NGZ_LEDGER.json.xz';baseline=json.loads(lzma.decompress(baseline_path.read_bytes()));state=copy.deepcopy(baseline)
 inherited=json.loads((E.parent/'verify-observed-20261105/NGX_CLOSED.json').read_text())['functions']
 for f in inherited+prior['functions']:
  for row in f['rows']:next(r for r in state['rows']if r['row']==row)['composed_status']='CLOSED'
 final=copy.deepcopy(state);updates=[]
 for f in new:
  for row in f['rows']:
   target=next(r for r in final['rows']if r['row']==row);assert target['function']==f['function']and target['composed_status']=='OPEN';target['composed_status']='CLOSED';target['NHG_certificate']=f
   updates.append(dict(row=row,function=f['function'],before='OPEN',after='CLOSED',certificate_file='NHG_CLOSED.json',certificate_sha256=sha(json.dumps(f,sort_keys=True).encode())))
 assert all(a==b for a,b in zip(state['rows'],final['rows'])if a['row']not in requirements)and state['trust_rows']==final['trust_rows']
 assert all(next(r for r in final['rows']if r['row']==id)['composed_status']=='OPEN'for id in ['TX1:129','TX1:130','TX1:133','TX1:134','TX1:136','TX1:137'])
 attempts=list(map(json.loads,(E/'NHG_ATTEMPTS.jsonl').read_text().splitlines()));counts=dict(kani=sum(x['kind']=='kani'for x in attempts),lean_support=sum(x['kind']not in ['kani','extract']for x in attempts),extraction=sum(x['kind']=='extract'for x in attempts));assert counts['kani']<=80 and counts['lean_support']<=90 and counts['extraction']<=1
 return dict(status='PASS',new_rows=sorted(f['rows'][0]for f in closed['functions']),stage4_new_rows=sorted(requirements),updates=json.loads(historical('NHG_LEDGER_DELTA.json'))['updates']+updates,retained_stage3_revision=seal['revision'],retained_NHG_raw_roots=81,new_raw_roots=26,total_NHG_raw_roots=107,scan_modules=len(scan),inherited_rows_preserved=len(state['rows'])-len(closed['functions']),budget_used=counts,security_target_established=False,trust_rows_unchanged=True)
if __name__=='__main__':
 result=validate();(E/'NHG_LEDGER_DELTA.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps({k:result[k]for k in ['status','new_rows','total_NHG_raw_roots','scan_modules','budget_used']}))
