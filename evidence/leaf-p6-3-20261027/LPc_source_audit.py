"""Read-only scratch source comparison against the inherited pinned native tree."""
from pathlib import Path
import hashlib,json
A=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-1-20261027/LPa_src')
B=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-3-20261027/LPc_src')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a={str(p.relative_to(A)):sha(p) for p in A.rglob('*') if p.is_file()}
b={str(p.relative_to(B)):sha(p) for p in B.rglob('*') if p.is_file()}
changed=[];errors=[]
for k,v in a.items():
 if b.get(k)==v:continue
 name=Path(k).name
 hooks={'fast_pairing.rs':'LPc_dot','r1_wire.rs':'LPc_wire','verifier.rs':'LPc_verifier','compact.rs':'LPc_compact','candidate.rs':'LPc_candidate'}
 if name not in hooks:errors.append(k);continue
 text=(B/k).read_text();hook=f'#[cfg(kani)] mod {hooks[name]} {{ include!("{hooks[name]}.rs"); }}'
 restored=text.replace('\n'+hook,'') if name=='fast_pairing.rs' else text.replace('\n'+hook+'\n','')
 matches=restored.encode()==(A/k).read_bytes()
 if not matches:errors.append(k+' non-hook mismatch')
 changed.append({'path':k,'inherited_sha256':v,'scratch_sha256':b.get(k),'cfg_hook_only':matches})
added=sorted(set(b)-set(a))
expected=['crates/aspis-r1-cost-probe/src/'+n for n in ['LPc_dot.rs','LPc_wire.rs','LPc_verifier.rs','LPc_compact.rs','LPc_candidate.rs']]
if set(added)!=set(expected):errors.append('unexpected added files')
print(json.dumps({'inherited_tree':str(A),'scratch_tree':str(B),'inherited_file_count':len(a),'scratch_file_count':len(b),'inherited_packet':'evidence/leaf-p6-1-20261027/LPa_host-source-audit.json','inherited_manifest_digest':hashlib.sha256(json.dumps(a,sort_keys=True).encode()).hexdigest(),'scratch_manifest_digest':hashlib.sha256(json.dumps(b,sort_keys=True).encode()).hexdigest(),'changed':changed,'added':{k:b[k] for k in added},'errors':errors,'axioms':'N/A: read-only source audit'},indent=2))
