from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';files={}
for q,append in [('crates/aspis-statement/src/lib.rs','\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\nmod NJB_copy;\n'),('crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs','\n#[cfg(kani)]\n#[path="NJB_terminal.rs"]\nmod NJB_native;\n')]:
 old=subprocess.check_output(['git','show',frozen+':'+q]).decode();new=old+append
 files[q]=dict(before_sha256=hashlib.sha256(old.encode()).hexdigest(),after_sha256=hashlib.sha256(new.encode()).hexdigest(),append=append)
patch=''.join(''.join(difflib.unified_diff(subprocess.check_output(['git','show',frozen+':'+q]).decode().splitlines(True),(subprocess.check_output(['git','show',frozen+':'+q]).decode()+r['append']).splitlines(True),fromfile='a/'+q,tofile='b/'+q))for q,r in files.items())
q='crates/aspis-statement/src/pool_v1/NJB_terminal.rs';h=(E/'NJB_terminal.rs.txt').read_text();patch+=''.join(difflib.unified_diff([],h.splitlines(True),fromfile='/dev/null',tofile='b/'+q))
(E/'NJB_native.patch').write_text(patch);(E/'NJB_PATCH_FILES.json').write_text(json.dumps(files,indent=1)+'\n')
kmx=E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch';(E/'NJB_KMX.sha256').write_text(hashlib.sha256(kmx.read_bytes()).hexdigest()+'  evidence/kani-mitig-20261028/KMX_copy_stubs.patch\n')
# Exact copy patch is reused, not rewritten.
(E/'NJB_KMX.patch').write_bytes(kmx.read_bytes())
(E/'NJB_install.py').write_text('''from pathlib import Path
import json,hashlib,subprocess
b=Path(__file__).resolve().parent;s=b/'NJB_src';patches=['NJB_KMX.patch','NJB_native.patch']
for patch in patches:subprocess.run(['git','apply','--check',str(b/patch)],cwd=s,check=True);subprocess.run(['git','apply',str(b/patch)],cwd=s,check=True)
x=json.loads((b/'NJB_PATCH_FILES.json').read_text());manifest=json.loads((b/'NJB_STAGING_MANIFEST.json').read_text())
pins={q:r['sha256'] for q,r in manifest['files'].items()};overrides={q:r['after_sha256']for q,r in x.items()};overrides['crates/aspis-statement/src/pool_v1/NJB_terminal.rs']=hashlib.sha256((b/'NJB_terminal.rs.txt').read_bytes()).hexdigest()
for q,r in x.items():assert (s/q).read_bytes()==(s/q).read_bytes()[:-len(r['append'])]+r['append'].encode();assert hashlib.sha256((s/q).read_bytes()[:-len(r['append'])]).hexdigest()==r['before_sha256']
(b/'NJB_FROZEN_FILE_PINS.json').write_text(json.dumps(pins));(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(overrides))
print('scratch-only modules installed; native bodies unchanged')
''')
# Keep predecessor graph validation, strengthen with cfg-only source erasure.
s=(E.parent/'verify-observed4-20261107/NIH_gate.py').read_text().replace('NIH_','NJB_')
(E/'NJB_gate.py').write_text(s)
base=json.loads((E.parent/'verify-observed4-20261107/NIH_K043.json').read_text());B='/home/dombarker/project-offloads/codex-cx-terminal-20261107'
for i in [1,2]:
 a=f'NJB_K{i:03}';x={k:v for k,v in base.items() if k not in ['source_revision','deps_fingerprint','source_tree_dirty']};x.update(attempt=a,module='NJB_semantic_public',sources=['NJB_gate.py','NJB_SOURCE_PINS.json','NJB_FROZEN_FILE_PINS.json','NJB_terminal.rs.txt','NJB_native.patch','NJB_KMX.patch'],command=['python3','NJB_gate.py',a+'.json'],deps_fingerprint={},expected_time='Optimized native getter with exact immutable borrowed-result constructors; no field operations or loops')
 x['native_command']=[v.replace('codex-cx-verify-observed4-20261107','codex-cx-terminal-20261107').replace('NIH_src','NJB_src').replace('NIH_target','NJB_target').replace('pool_v1::pair_forest_copy_terminal::NIH_native::NIH_link_weight','pool_v1::pair_forest_terminal::NJB_native::NJB_semantic_public') for v in x['native_command']]
 x['env'].pop('LEAN_PATH',None);x['env']['CARGO_TARGET_DIR']=B+'/NJB_target';x['env']['TMPDIR']=B+'/NJB_tmp';x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NJB_invert'if i==2 else '')
 x['collect']=[v.replace('NIH_K043',a)for v in x['collect']];(E/(a+'.json')).write_text(json.dumps(x,indent=1)+'\n')
print('native getter positive/control prepared; exact KMX patch pinned')
