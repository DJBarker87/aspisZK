#!/usr/bin/env python3
"""Recover archive inputs by receipt hashes, never by name proximity."""
import subprocess,json,hashlib,collections,re,lzma
from pathlib import Path
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def write(n,d): (E/n).write_text(json.dumps(d,indent=2)+'\n')
raw=subprocess.check_output(['git','ls-tree','-rz','HEAD','evidence','docs/research/100bit-spend-path-20261013/evidence'])
paths={};rs=collections.defaultdict(list);pins=collections.defaultdict(list);llbcs=collections.defaultdict(list)
provenance=json.load(open(E.parent/"emission-repro-20261110/NMH_PROVENANCE.json"))
packets={"/".join(p.split("/")[:2]) for b in provenance["blobs"] for p in b["committed_paths"] if p.startswith("evidence/")}
for row in raw.split(b'\0'):
 if not row:continue
 meta,p=row.split(b'\t');p=p.decode();oid=meta.decode().split()[2];paths[p]=oid
 if p.endswith('.rs'):rs[oid].append(p)
 if p.endswith(('.llbc','.llbc.xz')) and any(p.startswith(q+'/') for q in packets):llbcs[oid].append(p)
 if ((('pin' in p.lower()) and p.endswith('.json')) or (p.endswith('/stdout.log') and re.search(r'/[A-Za-z]+_E[0-9]+/',p))) and not '/emission-repro2-' in p:pins[oid].append(p)
del raw
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def blob(oid):
 proc.stdin.write((oid+'\n').encode());proc.stdin.flush();hdr=proc.stdout.readline().split();b=proc.stdout.read(int(hdr[2]));assert proc.stdout.read(1)==b'\n';return b
source={}
for oid,ps in rs.items():
 b=blob(oid);source[sha(b)]={'git_blob':oid,'paths':ps,'bytes':len(b)}
def hashes(d):
 if isinstance(d,str):return {d} if re.fullmatch('[0-9a-f]{64}',d) else set()
 if isinstance(d,dict):return set().union(*(hashes(v) for v in d.values()),set())
 if isinstance(d,list):return set().union(*(hashes(v) for v in d),set())
 return set()
embedded=0
for oid,ps in llbcs.items():
 try:
  b=blob(oid);b=lzma.decompress(b) if ps[0].endswith('.xz') else b
  d=json.loads(b);t=d.get('translated',d)
  for f in t.get('files',[]):
   if not f or not isinstance(f.get('contents'),str):continue
   content=f['contents'].encode();h=sha(content)
   if h not in source:source[h]=dict(git_blob=hashlib.sha1(b'blob '+str(len(content)).encode()+b'\0'+content).hexdigest(),paths=[],bytes=len(content),embedded=[])
   source[h].setdefault('embedded',[]).append(dict(container_paths=ps,container_git_blob=oid,source_path=f['name'],crate=f.get('crate_name'),sha256=h))
   embedded+=1
 except (ValueError,lzma.LZMAError,UnicodeDecodeError,KeyError):pass
records=[]
for oid,ps in pins.items():
 raw=blob(oid)
 try:docs=[json.loads(raw)]
 except (ValueError,UnicodeDecodeError):
  docs=[]
  for line in raw.splitlines():
   try:docs.append(json.loads(line))
   except (ValueError,UnicodeDecodeError):pass
 for d in docs:
  if not isinstance(d,dict):continue
  cc=d.get('charon_command');ac=d.get('aeneas_command')
  if not ac:ac=next((v for v in docs if isinstance(v,list) and v and isinstance(v[0],str) and 'aeneas' in v[0] and '-namespace' in v),None)
  if not isinstance(cc,list) or not isinstance(ac,list):continue
  h=d.get('rust_reference_sha256') or d.get('reference_sha256') or d.get('source_sha256') or d.get('rust_source_sha256')
  if not h or h not in source:continue
  def val(cmd,k):return cmd[cmd.index(k)+1] if k in cmd else None
  ns=val(ac,'-namespace');roots=[cc[i+1] for i,x in enumerate(cc[:-1]) if x=='--start-from']
  records.append(dict(receipt_paths=ps,receipt_git_blob=oid,receipt_sha256=sha(raw),namespace=ns,roots=roots,reference_sha256=h,source=source[h],charon_command=cc,aeneas_command=ac,outputs=d.get('outputs',{}),toolchain=d.get('toolchain')))
plan=json.load(open(E.parent/'emission-repro-20261110/NMH_PLAN.json'));inv=json.load(open(E.parent/'emission-repro-20261110/NMH_INVENTORY.json'))
prov=json.load(open(E.parent/'emission-repro-20261110/NMH_PROVENANCE.json'));byhash={b['blob']:b for b in prov['blobs']}
results=[]
for g in plan['groups']:
 matches=[r for r in records if r['namespace'] in g['namespace'] or set(g['members'])&hashes(r['outputs'])]
 # Hash link to archived Rust is mandatory; require producing packet association too.
 accepted=[]
 for r in matches:
  emitting_packets={p.split('/')[1] for h in g['members'] for p in byhash[h]['committed_paths'] if p.startswith('evidence/')}
  same_packet=any(p.startswith('evidence/') and p.split('/')[1] in emitting_packets for p in r['receipt_paths'])
  exact_output=bool(set(g['members'])&hashes(r['outputs']))
  if same_packet or exact_output:
   q=dict(r);q['basis']='Producing packet receipt with exact reference SHA256 matching archived Rust; '+('exact emitted-output SHA256 link' if exact_output else 'exact namespace in same producing packet; reproduction still required')
   accepted.append(q)
 results.append(dict(group=g['group'],members=g['members'],bytes=g['bytes'],crate=g['crate'],namespace=g['namespace'],annotated_symbols=g['annotated_symbols'],mappings=accepted,status='RECOVERED_HASH_LINKED_INPUT' if accepted else 'NO_HASH_LINKED_RECEIPT_FOUND',search=dict(reference_git_blobs=len(rs),reference_paths=sum(map(len,rs.values())),pin_git_blobs=len(pins),eligible_records=len(records))))
write('NML_INPUT_MAP.json',dict(schema=1,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),method='Exact producing receipt reference SHA256 to Git-object source bytes plus same packet/namespace or exact output hash; no name-proximity credit.',groups=results))
write('NML_RECOVERED_RECORDS.json',records)
print(json.dumps(dict(groups=len(results),recovered=sum(bool(g['mappings']) for g in results),records=len(records),rs_unique=len(rs),llbc_unique=len(llbcs),embedded=embedded)))
