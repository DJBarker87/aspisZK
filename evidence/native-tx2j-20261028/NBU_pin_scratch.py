from pathlib import Path
import importlib.util,sys,json,hashlib,subprocess
E=Path(__file__).resolve().parent
sys.argv=['pin','none'];s=importlib.util.spec_from_file_location('native',E/'NBU_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
rev=m.REV
expected={}
for line in subprocess.check_output(['git','ls-tree','-r',rev,'crates','programs'],text=True).splitlines():
 desc,p=line.split('\t');expected[p]=hashlib.sha256(subprocess.check_output(['git','show',rev+':'+p])).hexdigest()
r=m.py(f'''from pathlib import Path
import hashlib,json
b=Path({m.B!r})/'NBU_src';expected={expected!r};changes={{}};same=0
for n,h in expected.items():
 p=b/n;s=p.read_bytes()
 if hashlib.sha256(s).hexdigest()==h:same+=1
 else:changes[n]=s.decode()
print(json.dumps(dict(same=same,changes=changes)))
''');assert r.returncode==0
x=json.loads(r.stdout)
allowed=['crates/aspis-statement/src/lib.rs','crates/aspis-statement/src/pool_v1/pair_terminal.rs','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'];assert sorted(x['changes'])==sorted(allowed)
import difflib
patch=''
for n,txt in x['changes'].items():
 old=subprocess.check_output(['git','show',rev+':'+n],text=True)
 if n.endswith('lib.rs'):assert txt=='#![cfg_attr(kani, feature(allocator_api, next_index))]\n'+old+'\n#[cfg(kani)]\npub mod KMX_stubs;\n'
 else:assert txt.startswith(old) and txt[len(old):].startswith('\n#[cfg(kani)]')
 patch+=''.join(difflib.unified_diff(old.splitlines(True),txt.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
for mod in ['codecs','more','decode']:
 n=f'crates/aspis-statement/src/pool_v1/NBU_{mod}.rs';txt=(E/f'NBU_{mod}.rs.txt').read_text();patch+=''.join(difflib.unified_diff([],txt.splitlines(True),fromfile='/dev/null',tofile='b/'+n))
(E/'NBU_harness.patch').write_text(patch)
(E/'NBU_FROZEN_SOURCE_AUDIT.json').write_text(json.dumps(dict(revision=rev,unchanged=x['same'],cfg_only_changed=allowed,frozen_hashes=expected,KMX_patch_sha256=hashlib.sha256(Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes()).hexdigest()),indent=2)+'\n')
