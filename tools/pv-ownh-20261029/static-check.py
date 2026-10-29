"""D439 input identities and exhaustive machine-call frontier supplement.

Source reasoning and unreachable-edge justifications are in STATIC-CHECK.md.
This script does not claim to prove Rust semantic purity by pattern matching.
"""
from pathlib import Path
import hashlib,json,re,subprocess,time
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-ownh-20261029'
assert str(R)=='/Users/dominic/ZK/.worktrees/pv-own'
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/pv-ownh-20261029'
sha=lambda b:hashlib.sha256(b).hexdigest()
sources=json.loads((R/'evidence/pv-owne-20261029/static-capture.json').read_text())['sources']
native=json.loads((R/'evidence/pv-owng-20261029/native-result.json').read_text())
for s in sources:
 assert sha(s['text'].encode())==s['sha256']
 if 'git_blob' in s: assert sha(subprocess.check_output(['git','show','HEAD:'+s['relative_path']]))==s['sha256']
pins=[{k:s[k] for k in ['path','size','sha256']} for s in sources]+native['inputs']+[native['binary']]
code='''from pathlib import Path
import hashlib,json,subprocess
for p in PINS:
 b=Path(p['path']).read_bytes();assert len(b)==p['size'] and hashlib.sha256(b).hexdigest()==p['sha256'],p['path']
print(json.dumps({'checked_files':len(PINS),'sections':subprocess.check_output(['readelf','-SW',BINARY],text=True)}))
'''.replace('PINS',repr(pins)).replace('BINARY',repr(native['binary']['path']))
t=time.monotonic();q=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert q.returncode==0,q.stderr
checked=json.loads(q.stdout)
d=native['commands']['disassembly']['stdout'];rel=native['commands']['relocations']['stdout']
functions={int(m[1],16):(m[2],m[3]) for m in re.finditer(r'^([0-9a-f]+) <([^\n]+)>:\n(.*?)(?=\n[0-9a-f]+ <|\Z)',d,re.M|re.S)}
got={};external={}
for l in rel.splitlines():
 p=l.split()
 if len(p)>3 and p[2]=='R_X86_64_RELATIVE':got[int(p[0],16)]=int(p[3],16)
 elif len(p)>4 and p[2] in ['R_X86_64_GLOB_DAT','R_X86_64_JUMP_SLOT']:external[int(p[0],16)]=p[4].split('@')[0]
# Classifications are explicit. Failure/panic frontiers are not called pure.
cut={0x18a00:'allocator black box: alloc',0x18a10:'allocator black box: dealloc',0x18a20:'allocator black box: realloc',0x18a30:'allocator black box: alloc_zeroed',0x554db:'allocation/capacity failure; rdea-1 plus bounded-layout argument',0x596bf:'bounds panic; source row<1024 implies block<64',0x58ea0:'order panic; u16 strict total order',0x59880:'TrustedLen panic; fixed-size array flatten length and capacity bound',0x5a1d0:'unwind resume; only panic landing pads, not successful execution'}
seen=set();todo=[0x18a50,0x18c60];edges=[];references=[]
while todo:
 a=todo.pop()
 if a in seen:continue
 seen.add(a);name,body=functions[a]
 for l in body.splitlines():
  if '%fs:' in l or '%gs:' in l:raise AssertionError(('outside-box TLS',l))
  if '%rip' in l:references.append(dict(function=name,instruction=l))
  m=re.search(r'\b(call|jmp)\s+(.+)',l)
  if not m:continue
  arg=m[2];target=None;callee=None
  if arg.startswith('*'):
   g=re.search(r'# ([0-9a-f]+)',arg)
   if g:
    slot=int(g[1],16);target=got.get(slot);callee=external.get(slot)
   else:
    # Exactly two stack-array initializations in each builder. Register is
    # loaded from the pinned memset relocation; no other indirect edge allowed.
    assert a in [0x18dd0,0x19620] and '*%r14' in arg,l
    assert '5d240' in body and external[0x5d240]=='memset'
    callee='memset'
  else:
   g=re.match(r'([0-9a-f]+)',arg)
   if not g:continue
   target=int(g[1],16)
   # Jumps inside current function are control-flow, not call edges.
   if m[1]=='jmp' and target not in functions:continue
  if target is not None:
   if target==a:continue
   assert target in functions,(hex(a),l,hex(target))
   callee=functions[target][0]
   category=cut.get(target,'constant/local computation')
   if target not in cut:todo.append(target)
  else:
   assert callee in ['memset','memcpy','memmove','memcmp','bcmp'],(name,l,callee)
   category='caller-memory primitive; own-2 triple-prime(1), V370'
  edges.append(dict(caller=name,at=l.strip().split(':')[0],callee=callee,target=hex(target) if target else None,classification=category))
assert len(seen)>8
# Every RIP data access must be immutable data or a relocation slot. LEA is
# address construction; the source argument separately treats pointer use.
sections=[]
for l in checked['sections'].splitlines():
 m=re.search(r'\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)\s+\S+\s+(\S+)',l)
 if m:sections.append((m[1],int(m[2],16),int(m[3],16),m[4]))
for r in references:
 l=r['instruction'];m=re.search(r'# ([0-9a-f]+)',l)
 assert m,l
 addr=int(m[1],16);section=next((s for s in sections if s[1]<=addr<s[1]+s[2]),None)
 assert section,(r,hex(addr))
 r.update(address=hex(addr),section=section[0])
 assert section[0] in ['.rodata','.data.rel.ro','.got'] or 'lea' in l,(r,section)
 if section[0]=='.got':assert addr in got or addr in external,(r,hex(addr))
textmap={s['relative_path']:s['text'] for s in sources}
assert 'HOOK.load(Ordering::Acquire)' in textmap['std/src/alloc.rs'] # retained failure-only, never hidden
assert 'region.as_ptr() != v_base' in textmap['core/src/slice/sort/shared/smallsort.rs']
assert 'self.ptr == non_null!(self.end, T)' in textmap['alloc/src/vec/into_iter.rs']
out=dict(rule="own-2'''",revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),checker_sha256=sha(Path(__file__).read_bytes()),sources=[{k:s[k] for k in ['path','relative_path','size','sha256']} for s in sources],checked_files=checked['checked_files'],binary=native['binary'],functions=[dict(address=hex(a),name=functions[a][0]) for a in sorted(seen)],edges=edges,rip_references=references,frontier_justifications='STATIC-CHECK.md; failure and panic edges require their stated justification, not a purity assumption',result='source influence classification plus checked call/read frontier; consume with address and unreachable-edge source argument',inspection=dict(exit=0,wall_seconds=time.monotonic()-t,peak_rss='N/A read-only',swap='N/A',print_axioms='N/A'),compiler_boundary='V370/D381/D386 retained',rdea_1='retained')
(E/'static-capture.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(functions=len(seen),edges=len(edges),rip_references=len(references),checked_files=checked['checked_files'],frontier=sorted(set(x['classification'] for x in edges))),indent=2))
