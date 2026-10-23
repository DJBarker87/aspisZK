"""Check current sources against successful focused receipts and retain all failures."""
from pathlib import Path
import hashlib,json,re,subprocess,tempfile,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/adapter-rw-20261023';L=D/'lean';T=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()
subprocess.run([sys.executable,str(T/'gen_constants.py'),'--check'],check=True)
with tempfile.TemporaryDirectory(prefix='adapter-rw-emission-') as tmp:
 subprocess.run([sys.executable,str(T/'adapt_extract.py'),str(E/'generated-final'),tmp],check=True)
 for name in ['AdapterRwTypes.lean','AdapterRwModel.lean','AdapterRw-emission-adapter.json']:
  assert (Path(tmp)/name).read_bytes()==(L/name).read_bytes(),name
final={'AdapterRwTypes':2,'AdapterRwModel':40,'AdapterRwScalar':41,'AdapterRwConstants':43,'AdapterRwCuts':42,'AdapterRwRanges':44,'AdapterRwAccepted':45,'AdapterRwSdkSnapshots':25,'AdapterRwLeadInputs':47,'AdapterRwStage3Audit':48,'AdapterRwRuntimeAdmission':1}
standard={'propext','Classical.choice','Quot.sound'}
pattern=r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)"
receipts=[]
for n in range(2,49):
 p=E/f'lean-{n:03d}';x=json.loads((p/'receipt.json').read_text());out=(p/'stdout.log').read_text()
 for f,h in x['source_hashes'].items():assert sha((p/'sources'/f).read_bytes())==h
 full=re.findall(pattern,out)
 if x['exit_status']==0:
  for report in full:
   used=set(re.findall(r'\[(.*?)\]',report,re.S)[0].replace('\n','').replace(' ','').split(',')) if '[' in report else set()
   assert used<=standard,(n,used)
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 receipts.append({**x,'full_print_axioms':full,'accepted':x['exit_status']==0,'errors':re.findall(r'^.*error:.*$',out,re.M)})
# Every final module has a green receipt with exactly the current source.
pins=json.loads((E/'extraction/artifact-pins-final.json').read_text())
objects={Path(k).name:v for k,v in pins.items() if k.endswith('.olean')}
for mod,n in final.items():
 x=json.loads((E/f'lean-{n:03d}'/'receipt.json').read_text())
 assert x['exit_status']==0
 assert x['source_hashes'][mod+'.lean']==sha((L/(mod+'.lean')).read_bytes()),mod
 for obj in x['deps_fingerprint'].get('selected_objects',{}).values():
  name=Path(obj['path']).name
  if name in objects:assert obj['sha256']==objects[name]['sha256'],(mod,name)
 source=(L/(mod+'.lean')).read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',source),mod
# Pin every native function against the actual source captured by Charon.
source_rows=[]
for file in ['r1_pool_adapter_owned.rs','r1_pool_adapter.rs','lib.rs']:
 p=R/'programs/r1-cost-probe/src'/file;captured=E/'extraction/native-sources'/file
 assert p.read_bytes()==captured.read_bytes(),file
 source_rows.append({'file':str(p.relative_to(R)),'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size,'captured_source_identical':True})
body=(R/'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs').read_text();raw=(E/'generated-final/Funs.lean.txt').read_text()
owned=['stage1_owned','stage2_owned','validate_asq8','authenticate_asq8_accounts','authenticate_invariant_release_registry','require_readonly_buffer','require_readonly_account','require_verifier_checkpoint','require_distinct_accounts','require_zero']
for name in owned:assert 'def r1_pool_adapter.owned.'+name in raw,name
for name in ['key','owner','data','data_len']:
 assert re.search(r'def r1_pool_adapter.owned.OwnedAccount.(?:impl\.)?'+name+r'\b',raw),name
refinement={'native_source_revision':'572236f37d','sources':source_rows,'owned_function_roots':owned,'owned_methods':['key','owner','data','data_len'],'sdk_wrappers_outside_extraction':['snapshot','stage1','stage2'],'relation':'actual production-source Charon/Aeneas extraction, with explicit external operations; source-to-SBF and native snapshot/effect interpretation remain open','emission_adapter_sha256':sha((L/'AdapterRw-emission-adapter.json').read_bytes())}
(E/'source-refinement.json').write_text(json.dumps(refinement,indent=2)+'\n')
audit=(E/'lean-048/stdout.log').read_text();reports=re.findall(pattern,audit);assert len(reports)==52
manifest={'status':'partial; full native S2CallerFacts and release target not established','base_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'stage3_lean_attempts':len(receipts),'stage3_kani_runs':0,'budgets':{'lean':100,'kani':60},'final_modules':final,'final_axiom_reports':52,'final_axioms_standard_only':True,'final_objects':objects,'scope':'focused compatible cached union, not coherent frozen manifest replay','receipts':receipts}
(E/'stage3-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'stage3_lean_attempts':len(receipts),'successful':sum(r['accepted'] for r in receipts),'kani':0,'axiom_reports':len(reports),'final_source_matches':len(final)}))
