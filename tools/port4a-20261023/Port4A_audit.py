from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]; E=R/'evidence/port4a-20261023'; L=R/'docs/research/100bit-spend-path-20261013/lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('lean-*/receipt.json'))]
assert len(receipts)<=100
accepted={}
for p in sorted(L.glob('Port4A_*.lean')):
 found=[r for r in receipts if r['exit_status']==0 and r['source_hashes'].get(p.name)==sha(p)]
 assert found,('No accepted exact source',p)
 r=found[-1]
 assert all('sorryAx' not in a and set(re.findall(r'\[(.*?)\]',a,re.S)[0].replace('\n','').replace(' ','').split(','))<= {'propext','Classical.choice','Quot.sound'} for a in r['print_axioms'])
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text())
 accepted[p.name]={'sha256':sha(p),'receipt':r['attempt'],'axioms':r['print_axioms']}
for r in receipts:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0'
 for name in ['command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']:assert name in r
base=subprocess.check_output(['git','rev-parse','1e1545544b^'],cwd=R,text=True).strip()
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
assert all(p.startswith(('docs/research/100bit-spend-path-20261013/lean/Port4A_','tools/port4a-20261023/','evidence/port4a-20261023/')) for p in changed),changed
emission=json.loads((E/'reader-emission.json').read_text())
assert sha(R/emission['input'])==emission['input_sha256']
assert sha(L/'Port4A_NativeReader.lean')==emission['module_sha256']
inherit=json.loads((R/'evidence/ports3-20261023/continuation2.json').read_text())
# Exact shipped Rust/source spans from the inherited successful extraction.
spans=[]
for row in inherit['native_spans']:
 p=R/row['source']; assert p.is_file()
 # Whole source pins are recorded here; span selection was audited by Port3.
 spans.append({'path':row['source'],'sha256':sha(p),'bytes':p.stat().st_size})
result={'schema':'port4a-focused-proof-v1','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'baseline_revision':base,'actual_lean_compiles':len(receipts),'kani_runs':0,
 'reserved_without_compile':[p.stem for p in (R/'tools/port4a-20261023').glob('lean-*.json') if not (E/p.stem/'receipt.json').exists()],
 'accepted_final_modules':accepted,'excluded_attempts':[r['attempt'] for r in receipts if r['exit_status']!=0],
 'shipped_source_pins':spans,'elf_pins_inherited_not_rebuilt':inherit['elf_pins_inherited'],
 'source_change_assessment':'New Port4A proof/tool/evidence files only. No shipped source, parameters, features, wire format or artifact changes.',
 'scope':'Focused compatible import/axiom check only. Native reader helper implementation binding, Prepared canonicality and ten-step arithmetic remain open. Parameter-uniform writer provenance refuted; not a shipped-source forgery.'}
(E/'manifest.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'modules':len(accepted),'actual_lean_compiles':len(receipts),'kani_runs':0,'excluded':result['excluded_attempts'],'reserved_without_compile':result['reserved_without_compile']}))
