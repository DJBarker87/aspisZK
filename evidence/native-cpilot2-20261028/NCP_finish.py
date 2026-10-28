from pathlib import Path
import sys,json,hashlib,subprocess,shlex,time
import NCP_runner as m
REV=m.REV;E=m.E
names=subprocess.check_output(['git','ls-tree','-r','--name-only',REV,'crates','programs'],text=True).splitlines()
p=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
manifest={};baseline={}
for n in names:
 p.stdin.write((REV+':'+n+'\n').encode());p.stdin.flush()
 header=p.stdout.readline().split();size=int(header[2]);data=p.stdout.read(size);assert p.stdout.read(1)==b'\n'
 if not n.endswith('.rs') and n!='crates/aspis-core/Cargo.toml':
  # All source/dependency bytes are checked, not only Rust.
  pass
 manifest[n]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
 baseline[n]=data
p.stdin.close();p.wait();(E/'NCP_FROZEN_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
script='''from pathlib import Path
import json,hashlib,difflib,subprocess,shutil
b=Path(__file__).resolve().parent;src=b/'NCP_src';base=json.loads((b/'NCP_FROZEN_MANIFEST.json').read_text())
def pin(p):return {'sha256':hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),'bytes':p.stat().st_size}
changed={n:pin(src/n) for n,v in base.items() if (src/n).is_file() and pin(src/n)!=v}
missing=[n for n in base if not (src/n).is_file()]
added=[str(p.relative_to(src)) for folder in ['crates','programs'] for p in (src/folder).rglob('*') if p.is_file() and str(p.relative_to(src)) not in base]
# Return only changed source files; the Mac performs byte-exact insert-only checks against frozen git.
cache=Path('/home/dombarker/project-offloads/codex-cx-cpilot2-cache-20261028');original=json.loads((b/'NCP_CACHE_IMPORTED.json').read_text())
cache_now={str(p.relative_to(cache)):pin(p) for p in cache.rglob('*') if p.is_file()}
preserved=all(cache_now.get(n,{}).get('sha256')==v['sha256'] for n,v in original.items())
C=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025');roots=[cache,C,C/'objects',Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
keys={'Aeneas.olean'}
for root in roots:
 if (root/'Aeneas').exists():keys.update(str(p.relative_to(root)) for p in (root/'Aeneas').rglob('*.olean'))
libs={}
for key in sorted(keys):
 p=next((r/key for r in roots if (r/key).is_file()),None)
 assert p is not None,key
 libs[key]={'path':str(p),**pin(p)}
procs=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  args=(p/'cmdline').read_bytes().replace(b'\\x00',b' ').decode(errors='replace')
  if str(b) in args and any(x in args for x in ['cargo-kani','cbmc ','bin/lean ','S2W_lean_host.py','S2W_run_host.py']):procs.append({'pid':p.name,'args':args})
 except (FileNotFoundError,PermissionError,ProcessLookupError):pass
out={'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','checked_files':len(base),'missing':missing,'changed':changed,'new_scratch_files':added,'source_texts':{n:(src/n).read_text() for n in changed},'new_texts':{n:(src/n).read_text() for n in added},'cache_imports_preserved':preserved,'cache_files':len(cache_now),'resolved_aeneas':libs,'active_own_provers':procs,'cargo_lock':pin(src/'Cargo.lock'),'kmx_patch':pin(b/'NCP_KMX_copy_stubs.patch')}
(b/'NCP_FINAL_HOST_AUDIT.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
'''
(E/'NCP_audit_host.py').write_text(script)
m.admit('NCP_FINAL_AUDIT_UPLOAD')
payload=json.dumps({'NCP_FROZEN_MANIFEST.json':json.dumps(manifest,indent=2),'NCP_audit_host.py':script})
code='from pathlib import Path; import sys,json; b=Path('+repr(m.B)+'); x=json.load(sys.stdin); [(b/n).write_text(s) for n,s in x.items()]'
for retry in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',m.H,'python3 -c '+shlex.quote(code)],input=payload,text=True,capture_output=True)
 with (E/'NCP_FINAL_AUDIT_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps({'trial':retry,'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr})+'\n')
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
r=m.ssh('python3 '+m.B+'/NCP_audit_host.py');assert r.returncode==0,r.stderr
x=json.loads(r.stdout);texts=x.pop('source_texts');new=x.pop('new_texts');assert not x['missing'] and x['cache_imports_preserved'];assert not x['active_own_provers'],x['active_own_provers']
changes={};patch=[]
for n,s in texts.items():
 old=baseline[n].decode();a=old.splitlines(keepends=True);b=s.splitlines(keepends=True);insertions=[]
 for tag,i,j,k,l in __import__('difflib').SequenceMatcher(a=a,b=b,autojunk=False).get_opcodes():
  if tag=='equal':continue
  assert tag=='insert',(n,tag,i,j,k,l)
  for line in b[k:l]:
   z=line.strip()
   inner=z.startswith('#![cfg_attr(kani, feature(') and z.endswith('))]')
   if inner:
    flags=z[len('#![cfg_attr(kani, feature('):-3].split(',')
    assert set(f.strip() for f in flags)<={'stmt_expr_attributes','proc_macro_hygiene','allocator_api','next_index'},(n,z)
   assert not z or z.startswith('#[cfg') or inner,(n,z)
  insertions.extend(b[k:l])
 changes[n]={'insertion_lines':len(insertions),'only_cfg_instrumentation_and_blanks':True,'current_sha256':hashlib.sha256(s.encode()).hexdigest(),'frozen_sha256':manifest[n]['sha256']}
 patch.extend(__import__('difflib').unified_diff(a,b,fromfile='a/'+n,tofile='b/'+n))
for n,s in new.items():
 assert 'NCP_' in Path(n).name or Path(n).name=='KMX_stubs.rs',n
 if Path(n).name=='KMX_stubs.rs':
  lines=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text().splitlines(keepends=True);active=False;gold=[]
  for line in lines:
   if line.startswith('diff --git '):
    if active:break
    active=line.startswith('diff --git a/KMX_stubs.rs ')
   elif active and line.startswith('+') and not line.startswith('+++'):gold.append(line[1:])
  assert s==''.join(gold),'mandated KMX stub bytes differ'
 patch.extend(__import__('difflib').unified_diff([],s.splitlines(keepends=True),fromfile='/dev/null',tofile='b/'+n))
(E/'NCP_harness.patch').write_text(''.join(patch));x['instrumentation_audit']=changes
(E/'NCP_FINAL_HOST_AUDIT.json').write_text(json.dumps(x,indent=2)+'\n')
(E/'NCP_RESOLVED_AENEAS_PIN.json').write_text(json.dumps(x['resolved_aeneas'],indent=2)+'\n')
print(json.dumps({k:v for k,v in x.items() if k not in ['resolved_aeneas','new_scratch_files','changed','instrumentation_audit']},indent=2))
