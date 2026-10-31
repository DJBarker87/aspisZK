"""Extraction manifests pointing at unedited deployed lib.rs files."""
from pathlib import Path
import tomllib,json,os
W=Path.cwd();P=Path('tools/pv-b3p6-20261028');root=tomllib.loads(Path('Cargo.toml').read_text())
parity=tomllib.loads((P/'v244/Cargo.toml').read_text())['dependencies']
def val(x):
 if isinstance(x,bool):return str(x).lower()
 if isinstance(x,(str,int)):return json.dumps(x)
 if isinstance(x,list):return '['+','.join(val(v)for v in x)+']'
 return '{'+','.join(json.dumps(k)+'='+val(v) for k,v in x.items())+'}'
for group,crate in [('terminal','aspis-r1-cost-probe'),('field','aspis-core'),('poseidon','aspis-statement')]:
 C=Path('crates')/crate;D=P/('v244-direct17-'+group);D.mkdir(exist_ok=True);x=tomllib.loads((C/'Cargo.toml').read_text());deps={}
 all_deps=dict(x.get('dependencies',{}))
 for selector,sections in x.get('target',{}).items():
  assert selector=='cfg(not(target_os = \"solana\"))',selector
  all_deps.update(sections.get('dependencies',{}))
 for k,v in all_deps.items():
  if isinstance(v,str):v={'version':v}
  v=v.copy();base=C
  if v.pop('workspace',False):
   inherited=root['workspace']['dependencies'][k]
   inherited={'version':inherited}if isinstance(inherited,str)else inherited.copy();inherited.update(v);v=inherited;base=Path('.')
  if 'path'in v:v['path']=os.path.relpath((base/v['path']).resolve(),D.resolve())
  deps[k]=v
 for k,v in parity.items():
  if k.startswith('aspis-'):continue
  if k not in deps:deps[k]=v
  elif k=='getrandom':deps[k]['features']=sorted(set(deps[k].get('features',[])+v.get('features',[])))
 s='[package]\nname="pv-b3p6-reference227"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[lib]\npath='+val(os.path.relpath((C/'src/lib.rs').resolve(),D.resolve()))+'\n[dependencies]\n'
 s+=''.join(json.dumps(k)+'='+val(v)+'\n'for k,v in deps.items())
 if (C/'build.rs').exists():
  s=s.replace('[workspace]','build='+val(os.path.relpath((C/'build.rs').resolve(),D.resolve()))+'\n[workspace]')
 s+='[features]\n'+''.join(json.dumps(k)+'='+val(v)+'\n' for k,v in x.get('features',{}).items())
 s+='[profile.release]\nopt-level=3\noverflow-checks=false\ndebug-assertions=false\n'
 (D/'Cargo.toml').write_text(s)
