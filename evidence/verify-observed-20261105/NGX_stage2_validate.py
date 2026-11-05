"""Strict additive admission; historical stage1 checks are preserved."""
from pathlib import Path
import sys,json,hashlib,lzma,re,copy,importlib.util,subprocess
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(n):return json.loads((E/n).read_text())
def validate():
 spec=importlib.util.spec_from_file_location('NGX_stage1',E/'NGX_validate.py');old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old);prior=old.validate();assert prior['status']=='PASS'
 standard={'propext','Classical.choice','Quot.sound'};raw=read('NGX_audit/batch1/proof1.json')
 assert raw['exit_status']==0 and all(x['equal'] and set(x['walked_axioms'])<=standard for x in raw['results'])
 assert {x['root'] for x in raw['results']}==set(read('NGX_AUDIT_ROOTS.json')['groups'][1])
 assert read('NGX_L044/receipt.json')['exit_status']==0 and read('NGX_L045/receipt.json')['exit_status']==0 and read('NGX_L046/receipt.json')['exit_status']==0
 scan=list(map(json.loads,(E/'NGX_LOADED_scan.jsonl').read_text().splitlines()));assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
 # Unchanged compiled audit binary and walker: the stage1 eight fixtures apply
 # to exactly this binary, not a newly adapted or differently built driver.
 for name in ['NGX_ProofDriver','NGX_Driver']:
  original=read(('NGX_L009' if name=='NGX_ProofDriver' else 'NGX_L012')+'/'+name+'_BINARY_PIN.json')
  current=read('NGX_L045/'+name+'_BINARY_PIN.json');assert original==current
 selected=read('NGX_STAGE2_TARGETS.json')|{'NGX_COMBINED_IMPORT':'NGX_L044'}
 for module,attempt in selected.items():
  r=read(attempt+'/receipt.json');assert r['exit_status']==0
  assert sha((E/(module+'.lean')).read_bytes())==r['source_hashes']['NGX_generated/'+module+'.lean']
  assert all('sorryAx' not in line for line in r['print_axioms'])
 metadata=read('NGX_METADATA_MANIFEST.json');native=[]
 frozen_wire=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/r1_wire.rs'],cwd=R,text=True)
 for p,n in [(5,6),(8,9),(11,12),(13,14),(15,16),(17,18),(19,20),(21,22)]:
  pair=[]
  for number,status in [(p,0),(n,1)]:
   a=f'NGX_K{number:03}';r=read(a+'/receipt.json');ad=read(a+'-admission.json');g=read(a+'-graph-check.json');lock=read(a+'-lock-check.json');log=(E/a/'stdout.log').read_text()
   assert r['exit_status']==status and ad['exit']==0 and ad['reservation']['allowed'] is True
   assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and int(r['swaps'])==0
   assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
   assert g['graph_matches_frozen'] and lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
   m=metadata[a+'-graph.json'];full=lzma.decompress((E/m['artifact']).read_bytes());assert sha(full)==m['sha256']==g['graph_sha256']
   assert len(json.loads(full)['packages'])==g['resolved_packages']
   assert set(next(x['features'] for x in g['selected_closure'] if x['name']=='aspis-r1-cost-probe'))=={'default','private-leaf-salts','optimized-terminal','program-build'}
   assert not read(a+'-source-check.json')['errors']
   wire=(E/a/'sources/NGX_src/crates/aspis-r1-cost-probe/src/r1_wire.rs').read_text();assert wire==frozen_wire+'\n#[cfg(kani)]\nmod NGX_wire { include!(\"NGX_wire.rs\"); }\n'
   assert ('VERIFICATION:- FAILED' if status else 'VERIFICATION:- SUCCESSFUL') in log
   assert 'timed out' not in log.lower() and 'unwinding assertion' not in log.lower()
   for path,h in r['source_hashes'].items():assert sha((E/a/'sources'/path).read_bytes())==h
   source=(E/a/'sources/NGX_src/crates/aspis-r1-cost-probe/src/NGX_wire.rs').read_text()
   assert not re.search(r'\bstatic\s+(?:mut\s+)?\w',source) and 'Option<fn' not in source and 'stub_verified' not in source
   pair.append(r['module']);native.append(a)
  assert pair[0]==pair[1]
 # Frozen-body erasure of local-record cuts, with no changed predicate/callee.
 for filename,needle,replacement in [('NGX_PARSE_CUT.json','validate_record_fields(row, payload)?;','validate_cut(row, payload, log)?;'),('NGX_RECORD_AT_CUT.json','parse_record(row, framed)?;','record_cut(row, framed, log)?;')]:
  x=read(filename);original=x['original_body'];assert original in frozen_wire;body=original[original.index('{'):];assert body.replace(needle,replacement)==x['cut_body']
 assert all(r['normalized_body_equal'] for r in read('NGX_PREFIX_REUSED_CONTINUITY.json'))
 closed=read('NGX_CLOSED.json');ids={r for f in closed['functions'] for r in f['rows']};assert ids=={'TX1:139','TX1:143','TX1:144','TX1:146','TX1:151','TX1:152'}
 assert all(not f['inner_hypotheses_remaining'] for f in closed['functions'])
 required={
 'TX1:146':('AspisR1.NGX_StateImpl.source',[5],[6],[]),
 'TX1:139':('AspisR1.NGX_Payload.source',[15],[16],['TX1:140']),
 'TX1:143':('AspisR1.NGX_SemanticNew.source',[11,13,21],[12,14,22],['TX1:327']),
 'TX1:144':('AspisR1.NGX_SemanticDomain.total',[8],[9],['TX1:327']),
 'TX1:151':('AspisR1.NGX_ParseRecord.source',[17],[18],['TX1:153','TX1:154']),
 'TX1:152':('AspisR1.NGX_RecordAt.source',[19],[20],['TX1:151','TX1:153'])}
 for f in closed['functions']:
  root,positive,negative,edges=required[f['rows'][0]]
  assert f['lean_root']==root and root in {r['root'] for r in raw['results']}
  assert f['native_positive']==[f'NGX_K{i:03}' for i in positive] and f['matched_control']==[f'NGX_K{i:03}' for i in negative]
  assert f.get('internal_edges',[])==edges
 for row,names in [('TX1:143',['AspisR1.NGX_NewTrace.returned','AspisR1.NGX_NewTrace.rejected']),('TX1:144',['AspisR1.NGX_SampleTrace.rejected','AspisR1.NGX_SampleTrace.returned'])]:
  assert next(f for f in closed['functions'] if f['rows']==[row])['ordered_effect_roots']==names

 baseline=json.loads(lzma.decompress((R/'evidence/ledger8-20261105/NGJ_LEDGER.json.xz').read_bytes()));new=copy.deepcopy(baseline)
 for r in new['rows']:
  if r['row'] in ids:
   certificate=next(f for f in closed['functions'] if r['row'] in f['rows']);assert r['function']==certificate['function'] and r['composed_status']=='OPEN';r['composed_status']='CLOSED';r['NGX_certificate']=certificate
 assert all(a==b for a,b in zip(baseline['rows'],new['rows']) if a['row'] not in ids)
 # The digest dependency is selected from the explicitly accepted NGC packet,
 # whose admission is newer than this NGJ baseline; it is not NGX credit.
 child=json.loads((R/'evidence/slice-d-checkpoint-20261104/NGC_CLOSED.json').read_text());digest=next(f for f in child['functions'] if f['function']=='programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest');assert digest['status']=='CLOSED' and set(digest['rows'])=={'TX1:327','TX2:210'}
 counts=prior['budget_used'];assert counts['kani']<=100 and counts['lean_support']<=70
 return dict(status='PASS',new_rows=sorted(ids),new_since_stage1=sorted(ids-{'TX1:146'}),inherited_rows_preserved=len(baseline['rows'])-len(ids),baseline_sha256=sha(lzma.decompress((R/'evidence/ledger8-20261105/NGJ_LEDGER.json.xz').read_bytes())),external_callee=dict(provider='NGC',row='TX1:327',certificate_sha256=sha((R/'evidence/slice-d-checkpoint-20261104/NGC_CLOSED.json').read_bytes()),not_NGX_credit=True),native_receipts=native,raw_roots=len(raw['results']),scan_modules=len(scan),budget_used=counts,security_target_established=False)
if __name__=='__main__':
 x=validate();(E/'NGX_LEDGER_DELTA.json').write_text(json.dumps(x,indent=1));print(json.dumps(x))
