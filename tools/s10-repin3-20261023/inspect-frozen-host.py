#!/usr/bin/env python3
"""Retain source bodies, inline sites and raw-symbol matches from frozen rustc.
Records observations, never infers source semantics from a symbol match.
"""
import hashlib,json,re
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023')
OLD=H.parent/'codex-cx-s10-repin3-20261023/collected/elf-graphs.json'
sha=lambda b:hashlib.sha256(b).hexdigest()
def pin(p):return dict(path=str(p),sha256=sha(p.read_bytes()),bytes=p.stat().st_size)
def dump(p,x):
 raw=(json.dumps(x,indent=2,sort_keys=True)+'\n').encode();assert len(raw)<=5_000_000,(p,len(raw));p.write_bytes(raw)
def functions(p):
 lines=p.read_text().splitlines(keepends=True);i=0
 while i<len(lines):
  if lines[i].startswith('fn '):
   start=i;i+=1
   while i<len(lines) and lines[i].strip('\n')!='}':i+=1
   yield start+1,i+1,''.join(lines[start:i+1])
  i+=1
frontiers=json.loads((H/'frontier-input.json').read_text());old=json.loads(OLD.read_text())
result={};decls={}
for mode,build in [('default','build-default-v1'),('devnet','build-devnet-v1'),('pool','build-pool-v1')]:
 d=H/build;comparison=json.loads((d/'artifact-comparison.json').read_text());assert comparison['byte_identical'] or (mode=='devnet' and comparison['expected_sha256'] is None)
 fs=[];llvm={}
 for p in sorted((d/'compiler-output').glob('*.mir')):
  crate=p.stem.split('-')[0]
  for line,end,body in functions(p):fs.append(dict(crate=crate,path=str(p),line=line,end_line=end,header=body.splitlines()[0],body_sha256=sha(body.encode()),body=body))
 for p in sorted((d/'compiler-output').glob('*.ll')):
  lines=p.read_text().splitlines();comment=''
  for i,line in enumerate(lines):
   if line.startswith('; ') and not line.startswith('; Function Attrs:'):comment=line[2:]
   if line.startswith('define '):
    m=re.search(r'@(?:"([^"]+)"|([^ (]+))\(',line);assert m,line
    raw=m[1] or m[2];llvm.setdefault(raw,[]).append(dict(raw_symbol=raw,source_comment=comment,signature=line,path=str(p),line=i+1))
 linked=[]
 # LLVM definitions in our selected crates that survive in the pinned ELF.
 # External libraries not emitted by these crates remain separately inventoried.
 for s in old['artifacts'][mode]['symbols']:
  # legacy Rust symbol can be reconstructed unambiguously from nm-demangled components
  # use independent raw symbol table copied from first-pass evidence instead below
  pass
 rawrows=json.loads((H/'elf-raw-input.json').read_text())
 for r in rawrows:
  if r['artifact']!=mode:continue
  for name in r['raw_symbol_aliases']:
   if name in llvm:
    for definition in llvm[name]:linked.append(dict(id=r['id'],same_raw_symbol_definition_count=len(llvm[name]),**definition))
 decls[mode]=dict(llvm_linked_definitions=linked,llvm_definitions=len(llvm),mir_functions=len(fs))
 observations=[]
 for f in frontiers:
  canonical=f['mir_name'];crate=canonical.split('::')[0];method=canonical.rsplit('::',1)[-1];file=f['span'].split(':')[0]
  isimpl=' as ' in canonical or canonical.rsplit('::',2)[-2][:1].isupper()
  ty=None
  if isimpl:
   before=canonical.split(' as ')[0] if ' as ' in canonical else canonical.rsplit('::',1)[0]
   ty=before.split('::')[-1].strip('<>')
  matches=[]
  for b in fs:
   h=b['header']
   if b['crate']!=crate or not re.search(r'(?:^fn |::)'+re.escape(method)+r'\(',h):continue
   if isimpl:
    if f'<impl at {file}:' not in h:continue
    if ty and not (re.search(r'_1: &(?:mut )?(?:[A-Za-z_]+::)*'+re.escape(ty)+r'[,)>]',h) or re.search(r'_1: (?:[A-Za-z_]+::)*'+re.escape(ty)+r'[,)>]',h) or (method in ('new','from_le_bytes','from_m31','from_qm31','reduce_u64') and re.search(r'\b'+re.escape(ty)+r'\b',h))):continue
   else:
    relative=canonical[len(crate)+2:]
    if not (h.startswith('fn '+relative+'(') or h.startswith('fn '+method+'(') or (relative=='r0::heap::filled' and h.startswith('fn heap::filled('))):continue
   matches.append({k:v for k,v in b.items() if k!='body'})
  # Candidate exact source-token occurrences; provenance retained for review.
  terms=[canonical,canonical[len(crate)+2:]]
  if canonical.endswith('::heap::filled'):terms.append('heap::filled')
  if canonical.endswith('::private_leaf_hash_with_digest') or canonical.endswith('::parent_with_digest'):terms.append(method+'::<')
  if isimpl:
   terms=[ty+'::'+method,('<'+ty+' as '+canonical.split(' as ')[1].rsplit('::',1)[0]+'::'+method) if ' as ' in canonical else ty+'::'+method]
  occurrences=[]
  for b in fs:
   for n,line in enumerate(b['body'].splitlines(),b['line']):
    if ('(inlined ' in line or ' -> ' in line) and any(t in line for t in terms):occurrences.append(dict(path=b['path'],line=n,caller=b['header'],text=line.strip()))
  monos=[]
  for p in sorted((d/'diagnostics').glob('*.mono.txt')):
   for n,line in enumerate(p.read_text().splitlines(),1):
    if any(t in line for t in terms):monos.append(dict(path=str(p),line=n,text=line))
  observations.append(dict(**f,frozen_bodies=matches,compiler_occurrences=occurrences,monomorphizations=monos,status='FROZEN_GENERIC_BODY_OBSERVED' if len(matches)==1 else 'BODY_MATCH_REVIEW_REQUIRED',scope='Typed bodies and explicit type/const arguments from ELF-identical frozen compilation. Inline scope or mono collection alone is not final machine-code reachability or semantic refinement.'))
 result[mode]=observations
 # retain source bodies only once, as text rather than another giant JSON
 if mode=='default':
  with (H/'packet/frontier-frozen-bodies.txt').open('w') as out:
   wanted={(x['path'],x['line']) for r in observations for x in r['frozen_bodies']}
   for b in fs:
    if (b['path'],b['line']) in wanted:out.write(f'// {b["path"]}:{b["line"]}\n'+b['body']+'\n')
 dump(H/'packet'/('frontiers-'+mode+'.json'),observations)
bodyfile=H/'packet/frontier-frozen-bodies.txt'
bodyfile.write_text(bodyfile.read_text().rstrip()+'\n')
dump(H/'packet/llvm-linked-definitions.json',decls)
print(json.dumps({m:dict(unique=sum(len(r['frozen_bodies'])==1 for r in rs),review=[(r['index'],len(r['frozen_bodies'])) for r in rs if len(r['frozen_bodies'])!=1],occurrences=sum(len(r['compiler_occurrences']) for r in rs)) for m,rs in result.items()}))
