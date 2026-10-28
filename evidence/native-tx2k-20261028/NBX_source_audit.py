from pathlib import Path
import subprocess,json,hashlib,re
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
paths=['programs/r1-cost-probe/src/r1_pool_adapter.rs','programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','crates/aspis-statement/src/pool_v1/verifier_registry.rs','crates/aspis-statement/src/pool_v1/format.rs','crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs']
files={p:subprocess.check_output(['git','show',REV+':'+p]).decode() for p in paths}
for p,s in files.items():assert Path(p).read_text()==s,('STOP source differs',p)
def extract(s,name):
 m=re.search(r'\bfn '+re.escape(name)+r'\b',s);assert m,name
 start=s.index('{',m.start());depth=1;i=start+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[m.start():i]
owned=files[paths[1]];adapter=files[paths[0]]
model=Path('docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean').read_text()
# Complete source text and every occurrence retained; this is syntactic evidence,
# not a formal native-to-AeneasExtraction proof.
slotnames={15:'validate_verifier_policy_v1',23:'decode_pool_v1_pair_forest_terminal_request_v1',25:'is_paused',26:'is_immutable',27:'is_paused',28:'is_immutable',29:'is_active_at',30:'is_active_at',31:'decode_verifier_registry_v1',32:'decode_verifier_registry_entry_v1',33:'decode_verifier_registry_v2',34:'decode_verifier_registry_entry_v2',48:'decode_master_box',49:'decode_checkpoint_box',53:'emit_result'}
rows={}
for op,name in slotnames.items():
 native=[]
 for p in paths[:2]:
  s=files[p]
  for m in re.finditer(r'\b'+name+r'\s*\(',s):
   native.append(dict(path=p,line=s[:m.start()].count('\n')+1,context=s[max(0,m.start()-120):m.start()+220]))
 sdk=[]
 for m in re.finditer(r'ops\.op'+str(op)+r'\b',model):sdk.append(dict(line=model[:m.start()].count('\n')+1,context=model[m.start():m.start()+300]))
 assert sdk,(op,'no SDK callsite')
 assert native,(op,'no native callsite')
 rows[str(op)]=dict(native_function=name,native_occurrences=native,sdk_occurrences=sdk,status='source association inspection; not a kernel extraction component')
body=extract(adapter,'emit_result')
assert 'program::set_return_data(&encoded);' in body
assert 'Ok(())' in body
x=dict(revision=REV,files={p:dict(sha256=hashlib.sha256(s.encode()).hexdigest(),bytes=len(s.encode())) for p,s in files.items()},sdk_model_sha256=hashlib.sha256(model.encode()).hexdigest(),slots=rows,op53_effect=body,claim='read-only source inspection, no native completeness credit')
(E/'NBX_SOURCE_ASSOCIATION.json').write_text(json.dumps(x,indent=2)+'\n')
print('source audit',len(rows),'slots; op53 effect retained')
