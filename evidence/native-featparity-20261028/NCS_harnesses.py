import pathlib,json,re,hashlib,sys,collections,subprocess
sys.path.insert(0,'/private/tmp/NBI2-parser')
from tree_sitter import Language,Parser
import tree_sitter_rust
P=Parser(Language(tree_sitter_rust.language()));E=pathlib.Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()
rs=json.load(open(E/'NCS_RECEIPTS.json'));wanted={v for r in rs for k,v in r['source_hashes'].items()if k.endswith('.rs')}
blobs={};locations=collections.defaultdict(list)
# Reconstruct only complete /dev/null additions. Partial hunks are never treated as source.
for d in pathlib.Path('evidence').iterdir():
 if not d.is_dir()or not d.name.startswith(('native-','leaf-','kani-')):continue
 for p in d.rglob('*'):
  if not p.is_file()or p.suffix not in ('.rs','.patch')or p.stat().st_size>2000000:continue
  b=p.read_bytes()
  if p.suffix=='.rs':candidates=[b]
  else:
   candidates=[]
   for block in re.split(rb'(?=^--- )',b,flags=re.M):
    if not block.startswith(b'--- /dev/null\n'):continue
    lines=block.splitlines(keepends=True);match=next((i for i,l in enumerate(lines)if re.match(rb'@@ -0,0 \+1(?:,\d+)? @@',l)),None)
    if match is None:continue
    content=b''.join(l[1:]for l in lines[match+1:]if l.startswith(b'+')and not l.startswith(b'+++'))
    candidates.append(content)
  for content in candidates:
   h=sha(content)
   if h in wanted:blobs[h]=content;locations[h].append(str(p))
# Replay retained unified source patches in memory, checking every old context byte.
# Only exact final receipt SHA is accepted, regardless of reconstruction path.
baselines={};patch_stats=collections.Counter()
for d in pathlib.Path('evidence').iterdir():
 if not d.is_dir()or not d.name.startswith(('native-','leaf-','kani-')):continue
 states={}
 for p in sorted(d.glob('*.patch')):
  for block in re.split(rb'(?=^--- )',p.read_bytes(),flags=re.M):
   lines=block.splitlines(keepends=True)
   if len(lines)<3 or not lines[0].startswith(b'--- ')or not lines[1].startswith(b'+++ '):continue
   oldpath=lines[0][4:].strip().decode();newpath=lines[1][4:].strip().decode()
   if newpath.startswith('b/'):newpath=newpath[2:]
   if not newpath.endswith('.rs'):continue
   if oldpath=='/dev/null':base=b''
   else:
    if newpath not in baselines:
     q=subprocess.run(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+newpath],capture_output=True)
     baselines[newpath]=q.stdout if q.returncode==0 else None
    base=states.get(newpath,baselines[newpath])
   if base is None:continue
   def apply(base):
    old=base.splitlines(keepends=True);out=[];cursor=0;i=2
    while i<len(lines):
     m=re.match(rb'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',lines[i])
     if not m:i+=1;continue
     start=int(m[1])-1 if int(m[1])else 0
     if start<cursor:return None
     out+=old[cursor:start];cursor=start;i+=1
     while i<len(lines)and not lines[i].startswith((b'@@',b'diff --git',b'--- ')):
      line=lines[i];i+=1
      if line.startswith(b'\\'):continue
      if line[:1]in (b' ',b'-'):
       if cursor>=len(old)or old[cursor]!=line[1:]:return None
       cursor+=1
      if line[:1]in (b' ',b'+'):out.append(line[1:])
    return b''.join(out+old[cursor:])
   result=apply(base)
   if result is None and baselines.get(newpath)is not None:result=apply(baselines[newpath])
   if result is None:patch_stats['context_failure']+=1;continue
   states[newpath]=result;patch_stats['applied']+=1;h=sha(result)
   if h in wanted:blobs[h]=result;locations[h].append(str(p)+':checked-patch-reconstruction')
print('patch reconstruction',dict(patch_stats))
# Current host snapshots count only when their whole-file hash equals a historical receipt.
host=E/'NCS_I004-stdout.log'
if host.exists():
 for line in host.read_text().splitlines():
  r=json.loads(line)
  if r.get('exists') and r['sha256'] in wanted:
   h=r['sha256'];blobs[h]=r['text'].encode();locations[h].append(str(host)+':'+r['path'])
print('wanted source hashes',len(wanted),'matched',len(blobs))
parsed={}
def walk(n):
 yield n
 for c in n.named_children:yield from walk(c)
for h,b in blobs.items():
 t=P.parse(b);functions={}
 for n in walk(t.root_node):
  if n.type!='function_item':continue
  name=b[n.child_by_field_name('name').start_byte:n.child_by_field_name('name').end_byte].decode();body=n.child_by_field_name('body')
  if not body:continue
  attrs=[];a=n.prev_named_sibling
  while a and a.type in ('attribute_item','line_comment','block_comment'):
   if a.type=='attribute_item':attrs.append(b[a.start_byte:a.end_byte].decode())
   a=a.prev_named_sibling
  calls=[]
  for c in walk(body):
   if c.type=='call_expression':
    f=c.child_by_field_name('function');calls.append(b[f.start_byte:f.end_byte].decode())
  txt=b[body.start_byte:body.end_byte].decode()
  functions.setdefault(name,[]).append(dict(name=name,line=n.start_point.row+1,body_sha256=sha(b[body.start_byte:body.end_byte]),attributes=attrs,calls=calls,body=txt,feature_predicates=re.findall(r'feature\s*=\s*"([^"]+)"',txt),pointer_syntax=bool(re.search(r'Option\s*<\s*fn|Observer|\bSome\s*\(|\bfn\s*\(',txt))))
 parsed[h]=functions
out=[]
for r in rs:
 cmd=r['command'];harness=cmd[cmd.index('--harness')+1]if '--harness'in cmd else cmd[3]if len(cmd)>3 and '.py' in cmd[1] and not cmd[3].startswith('-') else None
 if not harness:
  original=json.loads(pathlib.Path(r['path']).read_text());harness=original.get('module')
 if not harness:continue
 name=harness.split('::')[-1];hits=[]
 for path,h in r['source_hashes'].items():
  if not path.endswith('.rs'):continue
  for fn in parsed.get(h,{}).get(name,[]):hits.append(dict(source=path,source_sha256=h,retained_at=locations[h],**fn))
 out.append(dict(receipt=r['path'],attempt=r['attempt'],harness=harness,exit=r['exit'],matched_sources=hits,missing_exact_snapshot=not hits,flags=r['env'],command=cmd))
(E/'NCS_HARNESS_AUDIT.json').write_text(json.dumps(dict(method='Exact whole-file receipt SHA matched against retained .rs or complete /dev/null patch additions; no partial hunk substituted. Bodies, direct calls, stubs, cfg features retained. Missing/ambiguous reach is not certified.',source_hashes_wanted=len(wanted),source_hashes_matched=len(blobs),rows=out),indent=2)+'\n')
print('harness receipts',len(out),'matched',sum(bool(r['matched_sources'])for r in out))
