"""Read-only native ownership/cleanup and adopted-client source evidence.
No compilation, extraction, source substitution or native adequacy claim.
"""
from pathlib import Path
import subprocess,json,hashlib,shlex,sys
E=Path('evidence/pv-evh10-20261102')
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(args):return subprocess.check_output(['git']+args)
branch='codex/pv-uc-20261029';rev=git(['rev-parse',branch]).decode().strip()
paths=['tools/r1-cost-probe/src/bin/devnet_spend/diagnostics.rs','tools/r1-cost-probe/build-client.sh','tools/r1-cost-probe/Cargo.toml']
client=[]
for p in paths:
 raw=git(['show',rev+':'+p]);client.append(dict(path=p,revision=rev,blob=git(['rev-parse',rev+':'+p]).decode().strip(),sha256=sha(raw),text=raw.decode()))
diag=client[0]['text']
for text in ['write_all(b"client error\\n")','write_all(b"client panic\\n")','System.alloc(layout)','System.alloc_zeroed(layout)','System.realloc(p, layout, size)','System.dealloc(p, layout)','if p.is_null() { std::process::abort(); }','if q.is_null() { std::process::abort(); }']:assert text in diag,text
# Same diagnostics as the source freeze in the adopted D474(C) packet.
assert git(['show','d42f8a4db548bccd06e15bcd64c9fd98abe423a9:'+paths[0]])==client[0]['text'].encode()
project=[]
for p,spans in [('crates/aspis-prover/src/state_only_hiding.rs',[(98,122),(136,145),(393,400)]),('crates/aspis-prover/src/state_only_entropy.rs',[(218,248)])]:
 raw=git(['show','HEAD:'+p]);lines=raw.decode().splitlines(keepends=True)
 project.append(dict(path=p,sha256=sha(raw),blob=git(['rev-parse','HEAD:'+p]).decode().strip(),spans=[dict(first=a,last=b,text=''.join(lines[a-1:b])) for a,b in spans]))
code=r'''
from pathlib import Path
import json,hashlib
root=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
paths=[root/'core/src/alloc/layout.rs',root/'alloc/src/raw_vec/mod.rs',root/'alloc/src/alloc.rs',next(Path('/home/dombarker/.cargo/registry/src').glob('*/zeroize-1.9.0/src/lib.rs'))]
anchors=[['pub const fn repeat(', 'pub const fn repeat_packed(', 'pub const fn pad_to_align(', 'const fn from_size_alignment(', 'const fn max_size_for_align('], ['fn try_allocate_in(', 'const fn handle_error(', 'const fn layout_array('], ['fn alloc_impl_runtime(', 'fn deallocate_impl_runtime('], ['Zeroize for IterMut', 'impl<Z> Drop for Zeroizing<Z>', 'Zeroize for [Z; N]', 'fn volatile_write', 'impl<Z> Zeroize for Z']]
rows=[]
for p,aa in zip(paths,anchors):
 raw=p.read_bytes();s=raw.decode();spans=[]
 for a in aa:
  i=s.find(a)
  if i<0:
   spans.append(dict(anchor=a,found=False));continue
  line=s.rfind('\n',0,i)+1;start=s.find('{',i);level=1;j=start+1
  while level:
   level+=(s[j]=='{')-(s[j]=='}');j+=1
  spans.append(dict(anchor=a,found=True,first=s.count('\n',0,line)+1,text=s[line:j]))
 rows.append(dict(path=str(p),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),spans=spans))
print(json.dumps(rows))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True);assert r.returncode==0,r.stderr
out=dict(status='SOURCE EVIDENCE ONLY; native association open',client=client,project=project,library=json.loads(r.stdout),selection='User D551 adopts D474(C); pv-uc source read-only, exact diagnostics byte-equal d42f8a4db5',limits=['writer partial-delivery/errors remain observable','allocator null abort has no Rust diagnostic request, external abort effects remain','capacity overflow uses installed fixed panic hook; selection/initialization not yet proved','partial fill error drops the original 64-byte Zeroizing array before return','native memory, compiler V370 and L3 zeroization association remain open'],rows_removed=[])
p=E/'native-sources.json';data=json.dumps(out,indent=2)+'\n'
if '--check' in sys.argv:assert p.read_text()==data
else:p.write_text(data)
print('PASS read-only source inventory; client diagnostics pinned; native association OPEN')
