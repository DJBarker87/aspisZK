"""Text/hash evidence only. Does not build, modify keys, or copy binaries."""
from pathlib import Path
import hashlib,json,subprocess,re,os
E=Path(__file__).resolve().parent.parent
ROOT=Path.cwd(); BASE=(E/'pins/revision.txt').read_text().strip()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(name,x):(E/name).write_text(json.dumps(x,indent=2)+'\n')
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
entries=subprocess.check_output(['git','ls-tree','-rz',BASE,'--','crates','programs']).split(b'\0')
files=[]
for entry in entries:
 if not entry:continue
 info,name=entry.split(b'\t',1);mode,kind,blob=info.decode().split();p=ROOT/os.fsdecode(name)
 data=os.fsencode(os.readlink(p)) if mode=='120000' else p.read_bytes()
 actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert actual==blob,(str(p),actual,blob)
 files.append(dict(path=os.fsdecode(name),sha256=hashlib.sha256(data).hexdigest(),size=len(data),base_blob=blob))
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard','--','crates','programs'],text=True).splitlines()
assert not untracked,untracked
write('shipped-sources-unchanged.json',dict(base_revision=BASE,comparison_revision=revision,files=files,untracked=untracked,changed=[],elf_rebuild_rule_triggered=False))
source_bindings=[]
for d in ['native','owned','y1','pair-owner','basis-owner']:
 for rel,original in [('field.rs','crates/aspis-core/src/field.rs'),('field/wide_exact.rs','crates/aspis-core/src/field/wide_exact.rs')]:
  p=E/d/rel;assert p.read_bytes()==Path(original).read_bytes()
  source_bindings.append(dict(copy=str(p.relative_to(E)),source=original,sha256=sha(p),size=p.stat().st_size))
assert (E/'y1/r0/scalar.rs').read_bytes()==Path('crates/aspis-core/src/r0/scalar.rs').read_bytes()
def fn(s,name):
 m=re.search(r'pub(?:\(crate\))? fn '+re.escape(name)+r'(?=[<(])',s);assert m,name
 b=s.index('{',m.start());depth=1;i=b+1
 while depth:
  if s[i]=='{':depth+=1
  elif s[i]=='}':depth-=1
  i+=1
 return s[m.start():i]
for dst,src,names in [('y1/r0/basis.rs','crates/aspis-core/src/r0/basis.rs',['double','values']),('y1/r0/encoder.rs','crates/aspis-core/src/r0/encoder.rs',['eval_pair','eval_message'])]:
 a=(E/dst).read_text();b=Path(src).read_text()
 for name in names:
  f=fn(a,name);assert f==fn(b,name)
  source_bindings.append(dict(copy=dst,source=src,function=name,sha256=hashlib.sha256(f.encode()).hexdigest()))
write('source-bindings.json',dict(revision=revision,bindings=source_bindings,qualification='Exact source bodies/features in the retained kits; this does not assert the unsuccessful native caller extraction or a simulator model join.'))
# Preserve the first function-slicing draft's exact erroneous basis source.
baseline=Path('crates/aspis-core/src/r0/basis.rs').read_text()
(E/'diagnostics/y1-basis-v1.rs.txt').write_text('use super::CodeField;\n'+fn(baseline,'doubled_factor')+'\n'+fn(baseline,'values')+'\n')
records=[]
for p in sorted((E/'native-receipts').glob('*/receipt.json')):
 r=json.loads(p.read_text());name=p.parent.name
 r.update(name=name,receipt=str(p.relative_to(E)),source_base_revision=BASE,archive_revision=revision,source_identity='Exact per-invocation input hashes and archived package sources; archive revision is not attributed as an unchanged checkout for earlier commands.')
 pin=E/'pins'/(name+'-inputs.json')
 if pin.exists():r['input_pin']=str(pin.relative_to(E));r['input_pin_sha256']=sha(pin)
 r['actual_target']=r['command']
 r['accepted']=r['exit_status']==0
 r['qualification']='Native/extraction evidence only; not a Lean theorem, source-to-model join, or release rebuild.'
 if r['exit_status']==124:r['peak_rss_scope_note']='time wrapper reports parent RSS; aggregate cgroup peak retained in receipt; no successful multiplication verdict.'
 records.append(r)
write('native-attempts.json',records)
write('preflight-retired.json',dict(attempts=[dict(attempt=9700,compiler_launched=False,reason='Historical receipt already occupied; launcher refused. No historical receipt is attributed to this task.'),dict(attempt=9747,compiler_launched=False,reason='Local source retrieval had not completed; file absent before launcher. Number retired.')],skipped_interval=[9701,9741],scope='Skipped occupied or intervening historical range without attributing its receipts; no compiler invocation by this task.'))
# Source pins for every new checked file; generated exception options stay as emitted.
L=ROOT/'docs/research/v8-r0-zk-20261009/lean'
modules=list((L/'R1Z').glob('ProverCommit*47.lean'))+list((L/'AspisR1ProducerChecked47').glob('*.lean'))+list((L/'AspisR1ProducerRelease47').glob('*.lean'))
for p in modules:
 if '/R1Z/' in str(p):
  assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',p.read_text()),p
  assert not re.search(r'set_option (maxRecDepth|maxHeartbeats)',p.read_text()),p
write('final-source-freeze.json',dict(revision=revision,base=BASE,sources=[dict(module=str(p.relative_to(L))[:-5].replace('/','.'),path=str(p.relative_to(ROOT)),sha256=sha(p),size=p.stat().st_size) for p in sorted(modules)]))
before=E/'endpoint/before.lean.txt';after=E/'endpoint/after.lean.txt';assert before.read_bytes()==after.read_bytes()
write('endpoint-unchanged.json',dict(before_sha256=sha(before),after_sha256=sha(after),size=before.stat().st_size,identical=True,scope='Conditional endpoint unchanged. D159 L1 is required but not installed or proved here.'))
print(json.dumps(dict(shipped_files=len(files),new_modules=len(modules),native_receipts=len(records),source_revision=revision)))
