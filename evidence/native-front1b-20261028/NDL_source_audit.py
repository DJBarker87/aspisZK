"""Read-only frozen-source comparison; never changes scratch or release source."""
from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',F,'crates','programs']).decode().splitlines()+['Cargo.lock']
expected={p:hashlib.sha256(subprocess.check_output(['git','show',F+':'+p])).hexdigest() for p in paths}
owned=['crates/aspis-core/src/lib.rs','crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs','crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/multiproof.rs','crates/aspis-r1-cost-probe/src/weights.rs','crates/aspis-r1-cost-probe/src/fast_pairing.rs']
frozen={p:subprocess.check_output(['git','show',F+':'+p]).decode() for p in owned}
x=dict(expected=expected,owned=owned,frozen=frozen)
code=r'''from pathlib import Path
import json,hashlib,re,difflib
x=json.loads(PAYLOAD);b=Path('/home/dombarker/project-offloads/codex-cx-native-front1b-20261028');s=b/'NDL_src';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
missing=[];exact=[];modified={};errors=[];patches={}
for n,h in x['expected'].items():
 p=s/n
 if not p.is_file():missing.append(n);continue
 actual=sha(p)
 if actual==h:exact.append(n);continue
 if n not in x['owned']:errors.append(dict(path=n,expected=h,actual=actual));continue
 text=p.read_text();patches[n]=''.join(difflib.unified_diff(x['frozen'][n].splitlines(True),text.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
 # Strip exact cfg(kani)-only module hooks and contract attributes, never body expressions.
 text=re.sub(r'\n#\[cfg\(kani\)\]\n(?:#\[path="[^"\n]+"\]\s*)?mod (?:NDD|NDL)_\w+;\n','\n',text)
 text=text.replace('\n#[cfg(kani)]\n#[path="field/NDL_core.rs"] mod NDL_core;\n','\n')
 text=''.join(line for line in text.splitlines(True) if not(
  ('cfg_attr(kani' in line or 'cfg_attr(all(kani,' in line) and ('kani::' in line or line.startswith('#![cfg_attr(kani')) or
  ('#[cfg(kani)]' in line and 'mod NDL_' in line)))
 if n.endswith('/field.rs'):
  for marker in ['fn qm31_from_karatsuba_channel_sums(', 'pub fn qm31_pack_base4(']:text=text.replace('    '+marker,marker)
 # Hook additions have a blank leading separator; removing a hook restores that separator too.
 while text.endswith('\n\n') and not x['frozen'][n].endswith('\n\n'):text=text[:-1]
 normalized=hashlib.sha256(text.encode()).hexdigest()
 modified[n]=dict(actual=actual,normalized=normalized,expected=h,cfg_only=normalized==h)
 if normalized!=h:errors.append(dict(path=n,normalized=normalized,expected=h,diff=''.join(difflib.unified_diff(x['frozen'][n].splitlines(True),text.splitlines(True),fromfile='frozen',tofile='normalized'))))
allowed_missing=['crates/aspis-r1-cost-probe/src/RealR1_client.rs','crates/aspis-r1-cost-probe/src/RealR1_client_tests.rs']
if set(missing)-set(allowed_missing):errors.append(dict(unexpected_missing=missing))
print(json.dumps(dict(frozen_files=len(x['expected']),exact=len(exact),modified_cfg_only=modified,missing_disabled_clients=missing,errors=errors,patches=patches,source_workspace=str(s),source_workspace_resolved=str(s.resolve()))))
'''.replace('PAYLOAD',repr(json.dumps(x)))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NDL_SOURCE_AUDIT.log').write_text(r.stderr);assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
(E/'NDL_SCRATCH_INSTRUMENTATION.patch').write_text(''.join(out.pop('patches').values()))
out['local_shipped_diff']=subprocess.check_output(['git','diff',F,'--','crates','programs','Cargo.lock']).decode()
(E/'NDL_SOURCE_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(frozen_files=out['frozen_files'],exact=out['exact'],cfg_only=len(out['modified_cfg_only']),missing=len(out['missing_disabled_clients']),errors=out['errors'])))
assert not out['errors'] and not out['local_shipped_diff']
