from pathlib import Path
import subprocess,hashlib,json,os,re,tarfile
w=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def cmd(args,env=None):return subprocess.check_output(args,text=True,env=env).strip()
source=[]
for name in ['aeneas','charon']:
 fs=json.loads((w/'inputs'/(name+'-source-pins.json')).read_text());bad=[]
 for p,h in fs.items():
  if sha(w/name/p)!=h:bad.append(p)
 assert not bad,bad
 links=[]
 with tarfile.open(w/'inputs'/(name+'-exact-source.tar.gz')) as t:
  for m in t:
   if m.issym():
    actual=os.readlink(w/m.name);assert os.path.normpath(actual)==os.path.normpath(m.linkname),(m.name,actual,m.linkname)
    links.append({'path':m.name,'archive_target':m.linkname,'staged_target':actual,'same_relative_target':True})
 source.append({'name':name,'regular_files_verified':len(fs),'symlinks_verified':links,'all_source_bytes_unchanged_after_build':True})
receipts={n:json.loads((w/(n+'-build-a/receipt.json')).read_text()) for n in ['charon','aeneas']}
assert all(r['exit_status']==0 for r in receipts.values())
assert 'ocamlopt' in receipts['aeneas']['compiler_process_examples']
assert '/work/charon/_build/install/default/lib/charon' in (w/'aeneas-build-a/aeneas.log').read_text()
assert (w/'aeneas-build-a/charon-ml-location.txt').read_text().strip()=='/work/charon/_build/install/default/lib/charon'
rt=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu');env=dict(os.environ);env['PATH']='/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin'
paths={'aeneas':w/'bin/aeneas','charon':w/'charon-target/release/charon','charon-driver':w/'charon-target/release/charon-driver'}
tools={n:{'path':str(p),'sha256':sha(p),'file':cmd(['file',str(p)])} for n,p in paths.items()}
tools['aeneas']['version']=cmd([str(paths['aeneas']),'-version']);tools['charon']['version']=cmd([str(paths['charon']),'version']);tools['charon']['toolchain_version']=cmd([str(paths['charon']),'toolchain-version'])
libs={}
for n,p in paths.items():
 a=['/home/dombarker/.cargo/bin/rustup','run','nightly-2026-06-01','ldd',str(p)] if n=='charon-driver' else ['ldd',str(p)]
 s=cmd(a,env);assert 'not found' not in s,(n,s);tools[n]['ldd']=s
 for name in re.findall(r'(?:=>\s+)?(/[^\s]+)',s):
  q=Path(name);libs[name]={'realpath':str(q.resolve()),'sha256':sha(q)}
runtime={str(p):sha(p) for p in [rt/'bin/rustc',rt/'bin/cargo',Path('/home/dombarker/.cargo/bin/rustup')]}
pins={'scope':'Exact unpatched b59/cb50 native Linux tools, freshly built; no extraction or Lean job by B',
 'source_archives':json.loads((w/'inputs/source-archives.json').read_text()),'post_build_source_verification':source,
 'tools':tools,'rustc_version':cmd([str(rt/'bin/rustc'),'-Vv']),'rust_runtime_binaries':runtime,'host_dynamic_libraries':libs,
 'ocaml_dependency_image':'sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7',
 'ocaml_environment_sha256':sha(w/'aeneas-build-a/environment.txt'),'rust_dependency_pins_sha256':sha(w/'charon-dependency-pins.json'),
 'receipts':{n:{'path':str(w/(n+'-build-a/receipt.json')),'sha256':sha(w/(n+'-build-a/receipt.json'))} for n in receipts},
 'invocation_environment':'Put /home/dombarker/.cargo/bin in PATH for the Charon wrapper; use sibling charon-driver. No CHARON_TOOLCHAIN_IS_IN_PATH override needed.',
 'matching_scope':'Compiler sources match the pinned local upstream revisions. Native platform, binary hashes and cached build dependencies are separately recorded; this is not a cross-platform reproducible-binary claim.',
 'local_snapshot_comparison':{'aeneas':'220c7ff9cce569dead1e72ef199775b3417493b7 contains all upstream b59 files unchanged','charon':'d333b4ec4317e6941452b324949f6830fec52455 contains all upstream cb50 regular files unchanged','symlink_audit_correction':'Local Path.readlink normalized leading ./; safe archive extraction data filter also normalizes relative symlink targets. Every staged target is recorded and resolves to the same relative path; all regular source bytes match.'}}
(w/'tools-final-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
print(json.dumps({'tools':{n:{k:v for k,v in d.items() if k in ['path','sha256','version','toolchain_version']} for n,d in tools.items()},'pins_sha256':sha(w/'tools-final-pins.json'),'source_verification':source},indent=2))
