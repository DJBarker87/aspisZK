"""Additive admission over immutable stage2 checks and current staged cuts."""
from pathlib import Path
import json,hashlib,lzma,subprocess,re,copy,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(n):return json.loads((E/n).read_text())
def historical(n):return subprocess.check_output(['git','show',read('NHG_STAGE2_SEAL.json')['revision']+':'+str((E/n).relative_to(R))],cwd=R)
def native(p,c):
 first=None
 for attempt,status in [(p,0),(c,1)]:
  rc=read(attempt+'/receipt.json');ad=read(attempt+'-admission.json');log=(E/attempt/'stdout.log').read_text();graph=read(attempt+'-graph-check.json');lock=read(attempt+'-lock-check.json')
  assert rc['exit_status']==status and ad['exit']==0 and ad['reservation']['allowed'] is True
  assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and int(rc['swaps'])==0
  assert rc['env']['CARGO_NET_OFFLINE']=='true' and rc['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert graph['graph_matches_frozen'] and lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  metadata=read('NHG_METADATA_MANIFEST.json')[attempt+'-graph.json'];data=lzma.decompress((E/metadata['artifact']).read_bytes());assert sha(data)==metadata['sha256']==graph['graph_sha256']
  assert not read(attempt+'-source-check.json')['errors']
  assert ('VERIFICATION:- SUCCESSFUL' if status==0 else 'VERIFICATION:- FAILED')in log
  assert 'timed out'not in log.lower() and 'unwinding assertion'not in log.lower()
  for path,h in rc['source_hashes'].items():assert sha((E/attempt/'sources'/path).read_bytes())==h
  assert rc['module']==read(p+'/receipt.json')['module']
  selected=next(x for x in graph['selected_closure']if x['name']=='aspis-r1-cost-probe')if rc['module'].startswith(('r1_wire::','NHG_native::'))else next(x for x in graph['selected_closure']if x['name']=='aspis-statement')
  expected={'default','private-leaf-salts','optimized-terminal','program-build'}if selected['name']=='aspis-r1-cost-probe'else set(next(x['features']for x in read('NHG_K003-graph-check.json')['selected_closure']if x['name']=='aspis-statement'))
  assert set(selected['features'])==expected
  for path in(E/attempt/'sources/NHG_src').rglob('NHG_*.rs'):
   text=path.read_text();assert not re.search(r'\bstatic\s+(mut\s+)?\w',text)and'Option<fn'not in text and 'stub_verified'not in text
  if first is None:first=rc
  else:
   if p=='NHG_K015':
    path='NHG_src/crates/aspis-r1-cost-probe/src/NHG_begin.rs'
    before=(E/p/'sources'/path).read_text();after=(E/c/'sources'/path).read_text()
    expected=before.replace('assert_eq!(t.state[k],after[k]);','assert_eq!(t.state[k],after[k]^if cfg!(NHG_invert){1}else{0});').replace('assert!(correct!=cfg!(NHG_invert));','assert!(correct);')
    assert expected==after
   else:assert first['source_hashes']==rc['source_hashes'],'Matched control must use identical source' 
   assert '--cfg NHG_invert'not in first['env']['RUSTFLAGS']and'--cfg NHG_invert'in rc['env']['RUSTFLAGS']
def validate(candidate_name="NHG_CLOSED.json"):
 seal=read('NHG_STAGE2_SEAL.json');assert seal['revision'].startswith('6ff7634f515')
 for n,pin in seal['files'].items():
  data=historical(n);assert len(data)==pin['bytes']and sha(data)==pin['sha256']
 assert(E/'NHG_validate.py').read_bytes()==historical('NHG_validate.py')
 for name in ['NHG_NGX_PINS.json','NHG_NGX_DEEP_PINS.json']:
  assert (E/name).read_bytes()==historical(name)
 for path,pin in read('NHG_NGX_DEEP_PINS.json')['files'].items():
  data=(R/path).read_bytes();assert sha(data)==pin['sha256'] and len(data)==pin['bytes']
 prior=json.loads(historical('NHG_CLOSED.json'));old_delta=json.loads(historical('NHG_LEDGER_DELTA.json'));assert old_delta['status']=='PASS'and len(prior['functions'])==4
 assert len(json.loads(historical('NHG_MUTATION_RESULTS.json')))==13 and all(x['rejected'] for x in json.loads(historical('NHG_MUTATION_RESULTS.json')))
 closed=read(candidate_name);assert closed['functions'][:4]==prior['functions']
 pairs=[(15,21),(27,28),(32,33),(34,35),(36,37),(38,39),(40,41),(42,43),(45,46),(47,48)]
 for p,c in pairs:native(f'NHG_K{p:03}',f'NHG_K{c:03}')
 # Exact error types, not a nominal/layout equivalence of two Error enums.
 carrier=(E/'NHG_K047/sources/NHG_src/crates/aspis-r1-cost-probe/src/NHG_public_carrier.rs').read_text()
 assert 'use aspis_core::state_only_prefix::r0::Error as ProducerError;'in carrier
 assert 'produced:Option<Result<Vec<u8>,ProducerError>>'in carrier
 assert "NHG_producer_cut(public:Public<'_>,log:&mut Log)->Result<Vec<u8>,ProducerError>"in carrier
 assert '&NHG_producer_cut(public,log).map_err(|_| Error::Public)?'in carrier
 frontier=(E/'NHG_K027/sources/NHG_src/crates/aspis-statement/src/pool_v1/NHG_frontier.rs').read_text()
 assert 'fn NHG_frontier_stage('in frontier and 'NHG_fields_cut(out,&values[row],log)?;'in frontier
 assert 'kani::assume(n>=1&&n<=1240+32*window)'in frontier
 assert 'unsafe {out.set_len(length);}'in frontier and 'kani::assume(log.observe>=out.len())'in frontier
 frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
 src=subprocess.check_output(['git','show',frozen+':crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'],cwd=R,text=True)
 cut=read('NHG_FRONTIER_CUT.json');assert cut['original']in src
 expected=[f'fields(out, &values[{i}])?;'for i in range(20)];assert all(x in cut['original']for x in expected)
 plan=read('NHG_PUBLIC_PLAN_CUT.json');assert plan['original']in src
 assert plan['body']==plan['original'].replace('self.semantic()','public.semantic()').replace('fields(&mut out,','NHG_fields(&mut out,').replace('frontier(&mut out,','NHG_frontier(&mut out,').replace(')?;',',log)?;')
 resolutions=read('NHG_RESOLUTIONS.json');assert resolutions['field_receiver']=='u32'and resolutions['index_receiver']=='u64'and resolutions['excluded_field_methods']==['TX2:016','TX2:039']
 assert 'value.0.to_le_bytes()'in src and 'source.next_pair_index.to_le_bytes()'in src
 for path,digest in resolutions['frozen_source_pins'].items():
  data=subprocess.check_output(['git','show',frozen+':'+path],cwd=R);assert sha(data)==digest
 field_text=subprocess.check_output(['git','show',frozen+':crates/aspis-core/src/field.rs'],cwd=R,text=True)
 profile_text=subprocess.check_output(['git','show',frozen+':crates/aspis-statement/src/pool_v1/pair_tree_profile.rs'],cwd=R,text=True)
 assert re.search(r'pub struct M31\(pub u32\)',field_text)
 assert re.search(r'pub next_pair_index:\s*u64',profile_text)

 checks={'NHG_FieldBounds':30,'NHG_FrontierFrame':37,'NHG_FrontierPackets':49,'NHG_PublicCarrier':41,'NHG_StdBytes':46,'NHG_ProducerDomains':47,'NHG_ProducerWidths':55,'NHG_ProducerPackets':48,'NHG_ProgramChain':56,'NHG_AppendFrame':50,'NHG_SnapshotViews':51,'NHG_BeginFrame':31,'NHG_Product':60,'NHG_FrontComposition':59,'NHG_COMBINED_IMPORT':61}
 for module,n in checks.items():
  rc=read(f'NHG_L{n:03}/receipt.json');assert rc['exit_status']==0 and sha((E/(module+'.lean')).read_bytes())==rc['source_hashes']['NHG_generated/'+module+'.lean']
  assert all('sorryAx'not in line for line in rc['print_axioms'])
 roots=read('NHG_STAGE3_ROOTS.json');walked=[]
 for i in roots['batches']:
  raw=read(f'NHG_audit/batch{i}/proof{i}.json');assert raw['exit_status']==0;walked+=raw['results']
 assert set(roots['roots'])=={r['root']for r in walked}
 assert all(r['equal']and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in walked)
 for n in range(61,68):assert read(f'NHG_L{n:03}/receipt.json')['exit_status']==0
 scan=list(map(json.loads,(E/'NHG_LOADED_scan.jsonl').read_text().splitlines()));assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
 assert len(scan)>=13527 and len(walked)==53
 new=closed['functions'][4:];requirements={'TX1:253':('AspisR1.NHG_FrontierPackets.closed_packets',['TX1:252'],[27],[28]),'TX1:254':('AspisR1.NHG_ProducerPackets.source',['TX1:252','TX1:253','TX1:255'],[32,34,36,38,40,42,45],[33,35,37,39,41,43,46]),'TX1:131':('AspisR1.NHG_PublicTranscript.source',['TX1:143','TX1:254'],[47],[48]),'TX1:150':('AspisR1.NHG_BeginFrame.composed',['TX1:141','TX1:145'],[15],[21])}
 assert {f['rows'][0]for f in new}==set(requirements)
 allroots=set(r for g in read('NHG_AUDIT_ROOTS.json')['groups']for r in g) | set(r for g in json.loads((E.parent/'verify-observed-20261105/NGX_AUDIT_ROOTS.json').read_text())['groups']for r in g)
 for f in new:
  row=f['rows'][0];root,edges,p,c=requirements[row];assert f['status']=='CLOSED'and f['lean_root']==root and f['internal_edges']==edges and f['inner_hypotheses_remaining']==[]
  assert f['native_positive']==[f'NHG_K{n:03}'for n in p]and f['matched_control']==[f'NHG_K{n:03}'for n in c]
  assert all(r in allroots for key in ['domain_roots','carrier_roots','ordered_effect_roots']for r in f.get(key,[]))and root in allroots
  assert f['KMX_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'and'RECLASSIFICATION'in f['trust']and'retained'in f['trust']
  assert f['source_transport']=='ruling (y)/(ai); emitted full Result/effect equality plus named native cuts; no whole timed-out shape credited'
  assert 'No caller capacity1884 assumption' in f['capacity_qualification']
 baseline_path=R/'evidence/ledger9-20261105/NGZ_LEDGER.json.xz';baseline=json.loads(lzma.decompress(baseline_path.read_bytes()));effective=copy.deepcopy(baseline)
 inherited=json.loads((E.parent/'verify-observed-20261105/NGX_CLOSED.json').read_text())['functions']
 for f in inherited:
  for row in f['rows']:next(r for r in effective['rows']if r['row']==row)['composed_status']='CLOSED'
 prior_state=copy.deepcopy(effective)
 for f in prior['functions']:
  for row in f['rows']:next(r for r in prior_state['rows']if r['row']==row)['composed_status']='CLOSED'
 updated=copy.deepcopy(prior_state);updates=[]
 for f in new:
  for row in f['rows']:
   target=next(r for r in updated['rows']if r['row']==row);assert target['composed_status']=='OPEN'and target['function']==f['function'];target['composed_status']='CLOSED';target['NHG_certificate']=f
   updates.append(dict(row=row,function=f['function'],before='OPEN',after='CLOSED',certificate_file='NHG_CLOSED.json',certificate_sha256=sha(json.dumps(f,sort_keys=True).encode())))
 ids={f['rows'][0]for f in new};assert all(a==b for a,b in zip(prior_state['rows'],updated['rows'])if a['row']not in ids)and effective['trust_rows']==updated['trust_rows']
 assert next(r for r in updated['rows']if r['row']=='TX1:137')['composed_status']=='OPEN'
 attempts=list(map(json.loads,(E/'NHG_ATTEMPTS.jsonl').read_text().splitlines()));counts=dict(kani=sum(x['kind']=='kani'for x in attempts),lean_support=sum(x['kind']not in ['kani','extract']for x in attempts),extraction=sum(x['kind']=='extract'for x in attempts));assert counts['kani']<=80 and counts['lean_support']<=90 and counts['extraction']<=1
 return dict(status='PASS',new_rows=sorted(f['rows'][0]for f in closed['functions']),stage3_new_rows=sorted(ids),updates=json.loads(historical('NHG_LEDGER_DELTA.json'))['updates']+updates,retained_stage2_revision=read('NHG_STAGE2_SEAL.json')['revision'],retained_stage2_raw_roots=28,new_raw_roots=len(walked),scan_modules=len(scan),inherited_rows_preserved=len(effective['rows'])-len(closed['functions']),budget_used=counts,security_target_established=False,trust_rows_unchanged=True)
if __name__=='__main__':
 result=validate();(E/'NHG_LEDGER_DELTA.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
