"""Additive stage3 admission: prior certificates and checks remain required."""
from pathlib import Path
import sys,json,hashlib,lzma,re,subprocess,importlib.util,copy
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest()
def read(n):return json.loads((E/n).read_text())
def validate():
 s=importlib.util.spec_from_file_location('NGX_stage2',E/'NGX_stage2_validate.py');old=importlib.util.module_from_spec(s);s.loader.exec_module(old);previous=old.validate();assert previous['status']=='PASS'
 oldclosed=read('NGX_CLOSED_STAGE2.json');closed=read('NGX_CLOSED.json');assert closed['functions'][:len(oldclosed['functions'])]==oldclosed['functions']
 # The historical snapshot is exactly the committed, previously admitted input.
 for p,filename in [('NGX_CLOSED.json','NGX_CLOSED_STAGE2.json'),('NGX_COMBINED_IMPORT.lean','NGX_STAGE2_IMPORT.lean.txt')]:
  assert subprocess.check_output(['git','show','6fc05468f23:evidence/verify-observed-20261105/'+p],cwd=R)==(E/filename).read_bytes()
 for line in (E/'NGX_STAGE2_IMPORT.lean.txt').read_text().splitlines():assert line in (E/'NGX_COMBINED_IMPORT.lean').read_text().splitlines()
 raw=read('NGX_audit/batch2/proof2.json');assert raw['exit_status']==0
 roots=set(read('NGX_AUDIT_ROOTS.json')['groups'][2]);assert set(x['root']for x in raw['results'])==roots
 assert all(r['equal']and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in raw['results'])
 for n in [64,65,66]:assert read(f'NGX_L{n:03}/receipt.json')['exit_status']==0
 selected=read('NGX_STAGE3_TARGETS.json')|{'NGX_COMBINED_IMPORT':'NGX_L064'}
 for module,attempt in selected.items():
  r=read(attempt+'/receipt.json');assert r['exit_status']==0 and sha((E/(module+'.lean')).read_bytes())==r['source_hashes']['NGX_generated/'+module+'.lean']
  assert all('sorryAx'not in line for line in r['print_axioms'])
 scan=list(map(json.loads,(E/'NGX_LOADED_scan.jsonl').read_text().splitlines()));assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
 for n in ['NGX_Driver','NGX_ProofDriver']:assert read('NGX_L065/'+n+'_BINARY_PIN.json')==read('NGX_L045/'+n+'_BINARY_PIN.json')
 native=[];metadata=read('NGX_METADATA_MANIFEST.json')
 for p,n in [(23,25),(27,28),(29,30)]:
  modules=[]
  for number,status in [(p,0),(n,1)]:
   a=f'NGX_K{number:03}';r=read(a+'/receipt.json');ad=read(a+'-admission.json');g=read(a+'-graph-check.json');lock=read(a+'-lock-check.json');log=(E/a/'stdout.log').read_text()
   assert r['exit_status']==status and ad['exit']==0 and ad['reservation']['allowed']is True
   assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and int(r['swaps'])==0
   assert r['env']['CARGO_NET_OFFLINE']=='true'and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
   assert g['graph_matches_frozen']and lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
   m=metadata[a+'-graph.json'];full=lzma.decompress((E/m['artifact']).read_bytes());assert sha(full)==m['sha256']==g['graph_sha256']and len(json.loads(full)['packages'])==g['resolved_packages']
   assert set(next(x['features']for x in g['selected_closure']if x['name']=='aspis-r1-cost-probe'))=={'default','private-leaf-salts','optimized-terminal','program-build'}
   assert not read(a+'-source-check.json')['errors']
   assert ('VERIFICATION:- FAILED'if status else'VERIFICATION:- SUCCESSFUL')in log
   assert 'timed out'not in log.lower()and'unwinding assertion'not in log.lower()
   for path,h in r['source_hashes'].items():assert sha((E/a/'sources'/path).read_bytes())==h
   source=(E/a/'sources/NGX_src/crates/aspis-r1-cost-probe/src/NGX_wire.rs').read_text();assert not re.search(r'\bstatic\s+(?:mut\s+)?\w',source)and'Option<fn'not in source and'stub_verified'not in source
   modules.append(r['module']);native.append(a)
  assert modules[0]==modules[1]
 frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/r1_wire.rs'],cwd=R,text=True)
 x=read('NGX_PREFIX_CUT.json');assert x['original_body']in frozen
 body=x['original_body'][x['original_body'].index('{'):];cut,count=re.subn(r'parse_record_at\(bytes, (\d+), (32|offset)\)',r'prefix_at_cut(bytes, \1, \2, log)',body)
 assert count==27 and cut.replace('Ok(Self {','Ok(Prefix {')==x['cut_body']and x['terminal']==13831
 x=read('NGX_SEMANTIC_CUT.json');assert x['original_body']in frozen
 body=x['original_body'][x['original_body'].index('{'):];assert body.replace('self.sample_block_validated(row, record.framed())?','semantic_block_cut(t, row, record.framed(), log)?').replace('qm31_sample(','semantic_qm_cut(').replace('?,\n        ))','?, log))')==x['cut_body']
 x=read('NGX_BEGIN_CUT.json');assert x['original_body']in frozen
 body=x['original_body'][x['original_body'].index('{'):];cut,count=re.subn(r'transcript.semantic_validated\(prefix.validated_record\((\d+)\)\?\)',r'begin_semantic_cut(transcript,prefix.validated_record(\1)?,log)',body)
 assert count==15 and cut==x['cut_body']
 # Reused sampler inputs are committed, unchanged and freshly validated.
 packet=R/'evidence/transcript-scalars-20261105';ngt=json.loads(subprocess.check_output([sys.executable,str(packet/'NGT_validate.py')],cwd=R,text=True));assert ngt['status']=='PASS'and ngt['positive_native']==20 and ngt['matched_failing_controls']==20
 assert ngt==read('NGX_NGT_REVALIDATION.json')
 ids={r for f in closed['functions']for r in f['rows']};assert ids=={'TX1:138','TX1:139','TX1:143','TX1:144','TX1:145','TX1:146','TX1:151','TX1:152','TX1:161','TX1:162','TX1:163'}
 required={'TX1:138':('AspisR1.NGX_PrefixSource.source',['TX1:152']),'TX1:145':('AspisR1.NGX_Validated.source',['TX1:144','TX1:148','TX1:149','TX1:163']),'TX1:161':('AspisR1.NGX_SamplerStages.digits_emitted',['TX1:162']),'TX1:162':('AspisR1.NGX_SamplerStages.pass_emitted',[]),'TX1:163':('AspisR1.NGX_SamplerStages.sample',['TX1:161','TX1:010'])}
 required_domains={
 'TX1:138':['AspisR1.NGX_PrefixGeometry.next','AspisR1.NGX_PrefixGeometry.terminal','AspisR1.NGX_PrefixCarrier.producer_domain'],
 'TX1:145':['AspisR1.NGX_Validated.sample_domain','AspisR1.NGX_SamplerJoin.total'],
 'TX1:161':['AspisR1.NGX_SamplerStages.pass_induction','AspisR1.NGX_SamplerStages.digits_induction','AspisR1.NGX_SamplerJoin.total'],
 'TX1:162':['AspisR1.NGX_SamplerStages.pass_induction','AspisR1.NGX_SamplerStages.digits_induction','AspisR1.NGX_SamplerJoin.total'],
 'TX1:163':['AspisR1.NGX_SamplerStages.pass_induction','AspisR1.NGX_SamplerStages.digits_induction','AspisR1.NGX_SamplerJoin.total']}
 for f in closed['functions'][len(oldclosed['functions']):]:
  assert f['domain_roots']==required_domains[f['rows'][0]]
  root,edges=required[f['rows'][0]];assert f['status']=='CLOSED'and f['lean_root']==root and root in roots and f['internal_edges']==edges and not f['inner_hypotheses_remaining']
  assert all(x in roots for k in ['domain_roots','carrier_roots','ordered_effect_roots']for x in f.get(k,[]))
  if f['rows'][0]=='TX1:138':assert f['carrier_roots']==['AspisR1.NGX_PrefixCarrier.fields','AspisR1.NGX_PrefixCarrier.full_result'] and f['native_positive']==['NGX_K023'] and f['matched_control']==['NGX_K025']
  if f['rows'][0]=='TX1:145':assert f['ordered_effect_roots']==['AspisR1.NGX_ValidatedTrace.rejected','AspisR1.NGX_ValidatedTrace.wrong_order','AspisR1.NGX_ValidatedTrace.returned'] and f['native_positive']==['NGX_K027'] and f['matched_control']==['NGX_K028']
  if f['rows'][0]in ['TX1:161','TX1:162','TX1:163']:
   for p,n in zip(f['native_positive'],f['matched_control']):
    assert json.loads((packet/p/'receipt.json').read_text())['exit_status']==0 and json.loads((packet/n/'receipt.json').read_text())['exit_status']==1
  else:assert all(x in native for x in f['native_positive']+f['matched_control'])
 baseline=json.loads(lzma.decompress((R/'evidence/ledger8-20261105/NGJ_LEDGER.json.xz').read_bytes()))
 for f in closed['functions']:
  for row in f['rows']:assert next(r['function']for r in baseline['rows']if r['row']==row)==f['function']
 new=copy.deepcopy(baseline);updates=[]
 for row in new['rows']:
  if row['row']in ids:
   assert row['composed_status']=='OPEN'
   packet=next(f for f in closed['functions']if row['row']in f['rows'])
   row['composed_status']='CLOSED';row['NGX_certificate']=packet
   row['composed_reason']='Exact hybrid source/model/caller-domain packet; combined L064, raw L065, coherence L066 and strict additive NGX_stage3_validate.py.'
   updates.append(dict(row=row['row'],function=row['function'],before='OPEN',after='CLOSED',certificate_sha256=sha(json.dumps(packet,sort_keys=True).encode()),certificate_file='NGX_CLOSED.json'))
 assert all(old==after for old,after in zip(baseline['rows'],new['rows'])if old['row']not in ids)
 assert 'TX1:137'not in ids and'TX1:150'not in ids
 attempts=list(map(json.loads,(E/'NGX_ATTEMPTS.jsonl').read_text().splitlines()));counts=dict(kani=sum(x['kind']=='kani'for x in attempts),lean_support=sum(x['kind']not in ['kani','extract']for x in attempts),extraction=sum(x['kind']=='extract'for x in attempts));assert counts['kani']<=100 and counts['lean_support']<=70 and counts['extraction']<=2
 return dict(status='PASS',updates=updates,new_rows=sorted(ids),new_since_stage2=sorted(ids-set(previous['new_rows'])),inherited_rows_preserved=len(baseline['rows'])-len(ids),baseline_sha256=previous['baseline_sha256'],raw_roots=len(raw['results']),scan_modules=len(scan),native_receipts=native,reused_NGT_native_pairs=20,budget_used=counts,external_callee=previous['external_callee'],security_target_established=False)
if __name__=='__main__':
 x=validate();(E/'NGX_LEDGER_DELTA.json').write_text(json.dumps(x,indent=1));print(json.dumps(x))
