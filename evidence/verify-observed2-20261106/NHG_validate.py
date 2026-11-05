"""Additive NHG admission. Inherited NGX certificates/checks are sealed, never replaced."""
from pathlib import Path
import json,hashlib,lzma,re,copy,subprocess,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent;G=E.parent/'verify-observed-20261105'
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(n):return json.loads((E/n).read_text())
def validate():
 pins=read('NHG_NGX_PINS.json')
 for n,v in pins.items():
  p=R/n;assert p.stat().st_size==v['bytes'] and sha(p.read_bytes())==v['sha256'],('inherited NGX input changed',n)
 deep=read('NHG_NGX_DEEP_PINS.json');assert deep['source_revision']=='9cb318748ee'
 original=subprocess.check_output(['git','ls-tree','-r','-z',deep['source_revision'],'--','evidence/verify-observed-20261105'],cwd=R)
 expected={}
 for entry in original.split(b'\0'):
  if entry:
   meta,path=entry.split(b'\t',1);expected[path.decode()]=meta.split()[2].decode()
 assert set(deep['files'])==set(expected)
 for path,item in deep['files'].items():
  data=(R/path).read_bytes();assert item['git_blob_sha1']==expected[path] and item['bytes']==len(data) and sha(data)==item['sha256']
  assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==expected[path]
 previous=json.loads((G/'NGX_LEDGER_DELTA.json').read_text());assert previous['status']=='PASS' and len(previous['new_rows'])==11
 # The prior validators and mutation suites remain byte-identical and required.
 for n in ['NGX_validate.py','NGX_stage2_validate.py','NGX_stage3_validate.py','NGX_stage2_tests.py','NGX_stage3_tests.py']:
  assert str((G/n).relative_to(R)) in pins
 native=[]
 for p,c in [(3,17),(5,18),(7,19),(13,20)]:
  modules=[]
  for number,status in [(p,0),(c,1)]:
   a=f'NHG_K{number:03}';rc=read(a+'/receipt.json');ad=read(a+'-admission.json');graph=read(a+'-graph-check.json');lock=read(a+'-lock-check.json');log=(E/a/'stdout.log').read_text()
   assert rc['exit_status']==status and ad['exit']==0 and ad['reservation']['allowed'] is True
   assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and int(rc['swaps'])==0
   assert rc['env']['CARGO_NET_OFFLINE']=='true' and rc['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
   assert graph['graph_matches_frozen'] and lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
   m=read('NHG_METADATA_MANIFEST.json')[a+'-graph.json'];full=lzma.decompress((E/m['artifact']).read_bytes());assert sha(full)==m['sha256']==graph['graph_sha256']
   assert not read(a+'-source-check.json')['errors']
   assert ('VERIFICATION:- SUCCESSFUL' if status==0 else 'VERIFICATION:- FAILED') in log
   assert 'timed out' not in log.lower() and 'unwinding assertion' not in log.lower()
   for path,h in rc['source_hashes'].items():assert sha((E/a/'sources'/path).read_bytes())==h
   root=next(x for x in graph['selected_closure']if x['name']=='aspis-r1-cost-probe') if p<13 else next(x for x in graph['selected_closure']if x['name']=='aspis-statement')
   if p<13:assert set(root['features'])=={'default','private-leaf-salts','optimized-terminal','program-build'}
   else:assert set(root['features'])==set(next(x['features']for x in read('NHG_K003-graph-check.json')['selected_closure']if x['name']=='aspis-statement'))
   for path in (E/a/'sources/NHG_src').rglob('NHG_*.rs'):
    s=path.read_text();assert not re.search(r'\bstatic\s+(mut\s+)?\w',s) and 'Option<fn'not in s and 'stub_verified'not in s
   modules.append(rc['module']);native.append(a)
  assert modules[0]==modules[1]
 # Each stronger negative is exactly the recorded property-only mutation of
 # the passing source. Its added guards/masks are inactive for invert=false.
 plans=read('NHG_STRICT_CONTROL_PLAN.json');assert len(plans)==5
 for plan in plans:
  psource=(E/plan['positive']/'sources/NHG_src'/plan['path']).read_text();csource=(E/plan['attempt']/'sources/NHG_src'/plan['path']).read_text();expected=psource
  assert sha(psource.encode())==plan['positive_sha256'] and sha(csource.encode())==plan['control_sha256'] and plan['unchanged_positive_configuration']is True
  if plan['positive']in ['NHG_K003','NHG_K005']:
   needle='let old=if j<n{out[j]}else{0};';expected=expected.replace(needle,'if cfg!(NHG_invert){kani::assume(value<2147483647);kani::assume(n>=1);kani::assume(j>=n);}'+'\n '+needle)
  elif plan['positive']=='NHG_K007':
   needle='let k:usize=kani::any();kani::assume(k<n);';expected=expected.replace(needle,needle+'if cfg!(NHG_invert){kani::assume(i==k);}')
  elif plan['positive']=='NHG_K013':
   for v in ['p','w']:expected=expected.replace(f'result.anchor[j]=={v}.anchor_root[j]',f'result.anchor[j].0==({v}.anchor_root[j].0 ^ if cfg!(NHG_invert){{1}}else{{0}})')
   expected=expected.replace('assert!(good!=cfg!(NHG_invert));','assert!(good);')
  else:
   assert plan['positive']=='NHG_K015'
   expected=expected.replace('assert_eq!(t.state[k],after[k]);','assert_eq!(t.state[k],after[k]^if cfg!(NHG_invert){1}else{0});').replace('assert!(correct!=cfg!(NHG_invert));','assert!(correct);')
  assert expected==csource
 frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
 src=subprocess.check_output(['git','show',frozen+':crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'],cwd=R,text=True)
 field=read('NHG_FIELD_SOURCE.json');assert field['original_fields']in src and field['iteration_body']in field['original_fields']
 semantic=(E/'NHG_K013/sources/NHG_src/crates/aspis-statement/src/pool_v1/NHG_semantic.rs').read_text();assert 'mem::zeroed'not in semantic and 'frontier:core::array::from_fn' in semantic and 'next_frontier:core::array::from_fn' in semantic
 source=(E/'NHG_K013/sources/NHG_src/crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs').read_text();assert source.replace('    #[cfg(kani)] mod NHG_semantic {include!("NHG_semantic.rs");}\n','')==src
 selected={'NHG_Serializer':'NHG_L003','NHG_PublicTranscript':'NHG_L005','NHG_Lengths':'NHG_L007','NHG_CopyFrame':'NHG_L014','NHG_FieldSpec':'NHG_L016','NHG_Semantic':'NHG_L013','NHG_Begin13':'NHG_L008','NHG_Begin9':'NHG_L009','NHG_Begin5':'NHG_L010','NHG_Begin':'NHG_L011','NHG_COMBINED_IMPORT':'NHG_L018'}
 for module,attempt in selected.items():
  rc=read(attempt+'/receipt.json');assert rc['exit_status']==0 and sha((E/(module+'.lean')).read_bytes())==rc['source_hashes']['NHG_generated/'+module+'.lean']
  assert all('sorryAx'not in l for l in rc['print_axioms'])
 roots=set(r for g in read('NHG_AUDIT_ROOTS.json')['groups']for r in g);walked=[]
 for i in range(3):
  raw=read(f'NHG_audit/batch{i}/proof{i}.json');assert raw['exit_status']==0;walked+=raw['results']
 assert {x['root']for x in walked}==roots and all(x['equal']and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for x in walked)
 fixtures=read('NHG_audit/fixtures/fixtures.json');assert fixtures['exit_status']==0 and len(fixtures['results'])==8
 for i,f in enumerate(fixtures['results']):assert f['equal'] and len(f['walked_axioms'])==(1 if i<4 else 0)
 assert read('NHG_WALKER_PIN.json')['byte_identical'] is True
 for attempt in ['NHG_L024','NHG_L025','NHG_L026','NHG_L027','NHG_L028']:assert read(attempt+'/receipt.json')['exit_status']==0
 scan=list(map(json.loads,(E/'NHG_LOADED_scan.jsonl').read_text().splitlines()));assert all(not x['dangling']and not x['duplicate_owners']and x['imports_match']for x in scan)
 oldimports=(G/'NGX_EXPECTED_IMPORTS.jsonl').read_text();assert (E/'NHG_EXPECTED_IMPORTS.jsonl').read_text().startswith(oldimports)
 closed=read('NHG_CLOSED.json');ids={r for f in closed['functions']for r in f['rows']};assert ids=={'TX1:249','TX1:252','TX1:255','TX1:266'}
 requirement={'TX1:249':('AspisR1.NHG_Semantic.transfer',[]),'TX1:266':('AspisR1.NHG_Semantic.withdrawal',[]),'TX1:255':('AspisR1.NHG_Semantic.source',['TX1:249','TX1:266']),'TX1:252':('AspisR1.NHG_FieldSpec.source',[])}
 for f in closed['functions']:
  row=f['rows'][0];root,edges=requirement[row];assert f['status']=='CLOSED'and f['lean_root']==root and f['internal_edges']==edges and not f['inner_hypotheses_remaining']
  assert root in roots and all(r in roots for k in ['domain_roots','carrier_roots','ordered_effect_roots']for r in f.get(k,[]))
  assert all(a in native for a in f['native_positive']+f['matched_control']) and f['KMX_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  assert 'RECLASSIFICATION' in f['trust'] and 'retained' in f['trust']
  if row=='TX1:252':
   assert f['native_positive']==['NHG_K003','NHG_K005','NHG_K007'] and f['matched_control']==['NHG_K017','NHG_K018','NHG_K019']
   assert '1<=out.len' in f['domain'] and f['capacity_qualification']=='No caller capacity1884 assumption. General reallocation/append value frame is NHG_CopyFrame.grow_append4 plus K007 one-byte window; pinned Std reserve/allocation/capacity/ownership/cleanup interpretation retained, as for NGC heap/resize. Allocation abort remains the accepted partial terminal, not a recoverable Error.'
  else:assert f['native_positive']==['NHG_K013']and f['matched_control']==['NHG_K020']
 baseline_path=R/'evidence/ledger9-20261105/NGZ_LEDGER.json.xz';baseline=json.loads(lzma.decompress(baseline_path.read_bytes()));effective=copy.deepcopy(baseline)
 inherited=json.loads((G/'NGX_CLOSED.json').read_text())['functions']
 for f in inherited:
  for row in f['rows']:
   target=next(r for r in effective['rows']if r['row']==row);assert target['function']==f['function'];target['composed_status']='CLOSED';target['NGX_certificate']=f
 new=copy.deepcopy(effective);updates=[]
 for f in closed['functions']:
  for row in f['rows']:
   target=next(r for r in new['rows']if r['row']==row);assert target['function']==f['function'] and target['composed_status']=='OPEN';target['composed_status']='CLOSED';target['NHG_certificate']=f
   updates.append(dict(row=row,function=f['function'],before='OPEN',after='CLOSED',certificate_file='NHG_CLOSED.json',certificate_sha256=sha(json.dumps(f,sort_keys=True).encode())))
 assert all(a==b for a,b in zip(effective['rows'],new['rows'])if a['row']not in ids) and effective['trust_rows']==new['trust_rows']
 assert next(r for r in new['rows']if r['row']=='TX1:137')['composed_status']=='OPEN'
 attempts=[json.loads(l)for l in(E/'NHG_ATTEMPTS.jsonl').read_text().splitlines()];counts=dict(kani=sum(x['kind']=='kani'for x in attempts),lean_support=sum(x['kind']not in ['kani','extract']for x in attempts),extraction=sum(x['kind']=='extract'for x in attempts));assert counts['kani']<=80 and counts['lean_support']<=90 and counts['extraction']<=1
 return dict(status='PASS',updates=updates,new_rows=sorted(ids),inherited_NGX_rows=sorted(r for f in inherited for r in f['rows']),inherited_NGX_checks='unchanged validators, inputs, PASS and mutation receipts sealed by NHG_NGX_PINS.json; no passing shape rerun',baseline_sha256=sha(baseline_path.read_bytes()),inherited_rows_preserved=len(effective['rows'])-len(ids),raw_roots=len(roots),scan_modules=len(scan),native_receipts=native,budget_used=counts,security_target_established=False)
if __name__=='__main__':
 x=validate();(E/'NHG_LEDGER_DELTA.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x))
