"""Inventory actual owned helper bodies; do not confuse lifted bodies with opaque ops."""
from pathlib import Path
import re,hashlib,json,sys,subprocess
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean';E=R/'evidence/s2w-20261023'
native=R/'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs';model=L/'AdapterRwModel.lean'
# This is the historical extraction inventory. The inherited H5 helper rewrite
# is assessed separately; never silently repin an old emitted body to new source.
inv=json.loads((E/'source-inventory.json').read_text())
s=subprocess.check_output(['git','show',inv['revision']+':'+str(native.relative_to(R))],cwd=R).decode()
m=model.read_text();sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[]
for match in re.finditer(r'(?m)^\s*(?:pub\(super\) )?fn ([a-zA-Z_][a-zA-Z_0-9]*)(?:<[^\n]*?>)?\(',s):
 name=match[1]
 if name in ('snapshot','stage1','stage2'):continue
 start=s.index('{',match.end());depth=1;i=start+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 body=s[match.start():i]
 suffix='OwnedAccount.impl.'+name if name in ('key','owner') else 'OwnedAccount.'+name if name in ('data','data_len') else name
 lean='r1_pool_adapter.owned.'+suffix
 found=re.search(r'(?m)^def '+re.escape(lean)+r'(?= |\n)',m)
 assert found,lean
 end=m.find('\n/--',found.start());end=len(m) if end<0 else end
 block=m[found.start():end]
 assert ':=' in block,lean
 rows.append({'native_function':name,'native_line':s[:match.start()].count('\n')+1,'native_fragment_sha256':sha(body.encode()),'extracted_definition':lean,'extracted_body_sha256':sha(block.encode()),'external_operations':sorted(set(re.findall(r'ops\.(op\d+)',block)),key=lambda n:int(n[2:])),'status':'Aeneas body already extracted, not an arbitrary Result-return contract'})
raw=R/'docs/research/100bit-spend-path-20261013/evidence/adapter-rw-20261023/generated-final'
files={str(p.relative_to(R)):sha(p.read_bytes()) for p in raw.rglob('*') if p.is_file()}
assert files
out={'native_source':str(native.relative_to(R)),'native_sha256':sha(s.encode()),'extracted_model':str(model.relative_to(R)),'model_sha256':sha(model.read_bytes()),'inherited_final_emission':files,'owned_functions':rows,'scope':'Existing whole-owned Aeneas extraction closes the helper-body extraction choice. Atomic lifting does not enumerate effects inside those bodies. No native-entry association or S2CallerFacts is inferred.','separate_children':{'op10':'first-entry verifier','op11':'authenticated resume verifier','op47/op22':'full forest codec','op51':'proof scanner','op52':'statement reconstruction'},'outside_owned_extraction':['native stage1/stage2 entry wrappers','native snapshot (separately extracted by S2W)','SDK/std/allocator lowering']}
p=E/'helper-bodies.json';text=json.dumps(out,indent=2)+'\n'
if '--check' in sys.argv:assert p.read_text()==text
else:p.write_text(text)
print(json.dumps({'owned_bodies':len(rows),'opaque_owned_body_replacements':0,'emission_files':len(files)}))
