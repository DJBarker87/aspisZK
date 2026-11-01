#!/usr/bin/env python3
"""Conservative K-3 source classifier. EXPOSED includes unresolved source closure.
NOT-EXPOSED requires every receipt-pinned Rust input to be recovered and no
`static` token in any input. Static reads and immutable declarations are deliberately
overapproximated; this is a suspension inventory, not a bug detector.
No initializer-byte whitelist is sound enough to exempt a writable static.
"""
from pathlib import Path
import json,hashlib,lzma,re,subprocess,collections,sys
ROOT=Path(__file__).resolve().parents[2];E=Path(__file__).resolve().parent
FROZEN='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
sha=lambda b:hashlib.sha256(b).hexdigest()
def classify(texts,missing=()):
 hits=[dict(source=n,line=i+1,text=l.strip()[:300]) for n,t in texts.items() for i,l in enumerate(t.splitlines()) if re.search(r'\bstatic\b',l)]
 # Includes macro-generated statics whenever literal token appears. Unknown
 # inputs/macros are not licensed by a NOT-EXPOSED result.
 macro=[n for n,t in texts.items() if re.search(r'(?:include!|macro_rules!|\bproc_macro\b)',t)]
 reasons=[]
 if hits:reasons.append('STATIC_TOKEN: conservatively includes mutable, interior-mutable, immutable and unwritten statics')
 if missing:reasons.append('UNRESOLVED_PINNED_SOURCE')
 if macro:reasons.append('MACRO_OR_INCLUDE_CLOSURE_REQUIRES_REVIEW')
 if not texts:reasons.append('NO_PINNED_RUST_SOURCE')
 return dict(classification='AFFECTED' if reasons else 'UNAFFECTED',reason=reasons or ['ALL_PINNED_RUST_INPUTS_RECOVERED_WITHOUT_STATIC_TOKEN'],static_sites=hits,missing_sources=list(missing),macro_sources=macro)
@__import__("functools").lru_cache(maxsize=None)
def frozen(path):
 r=subprocess.run(['git','show',FROZEN+':'+path],cwd=ROOT,capture_output=True)
 return r.stdout if r.returncode==0 else None
def patched_files(t,bases=None):
 """Strictly replay unified Rust-file hunks against frozen bytes, never the checkout."""
 lines=t.splitlines(keepends=True);i=0
 while i<len(lines):
  if not lines[i].startswith('--- '):i+=1;continue
  old=lines[i][4:].strip().split('\t')[0];i+=1
  if i>=len(lines) or not lines[i].startswith('+++ '):continue
  new=lines[i][4:].strip().split('\t')[0];i+=1
  path=new.removeprefix('b/');base=[] if old=='/dev/null' else ((bases or {}).get(path) if path in (bases or {}) else (frozen(path) or b'').decode(errors='replace')).splitlines(keepends=True)
  pos=0;out=[];ok=True;hunks=0
  while i<len(lines) and not lines[i].startswith('--- ') and not lines[i].startswith('diff --git '):
   m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',lines[i])
   if not m:i+=1;continue
   hunks+=1;start=int(m[1])-1 if int(m[1]) else 0
   if start<pos:ok=False
   out+=base[pos:start];pos=start;i+=1
   while i<len(lines) and lines[i][:1] in [' ','+','-','\\'] and not lines[i].startswith('--- '):
    l=lines[i];i+=1
    if l[0]=='\\':continue
    if l[0] in ' -':
     if pos>=len(base) or base[pos]!=l[1:]:ok=False
     pos+=1
    if l[0] in ' +':out.append(l[1:])
  out+=base[pos:]
  if ok and hunks and path.endswith('.rs'):yield path,''.join(out)
def read_json(p):return json.loads(lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else p.read_bytes())
def main():
 ndt=read_json(ROOT/'evidence/native-ledger3-20261029/NDT_LEDGER.json');neb=read_json(ROOT/'evidence/slice-q-compose-20261029/NEB_LEDGER.json.xz');nec=read_json(ROOT/'evidence/slice-s-leaves-20261029/NEC_CLOSED.json')
 wanted=collections.defaultdict(lambda:dict(groups=set(),rows=set(),claims=set()))
 for label,d in [('NDT',ndt),('NEB',neb)]:
  closed=[r for r in d['rows'] if label=='NDT' or r.get('composed_status')=='CLOSED']
  for c in d['claims']:
   if label=='NEB' and not any(c['claim_id'] in row.get('selected_claims',row.get('claim_ids',[])) for row in closed):continue
   for rp in c.get('active_support_receipts',[]):
    w=wanted[rp];w['groups'].add(label);w['claims'].add(c['claim_id'])
    for row in closed:
     if c['claim_id'] in row.get('selected_claims',row.get('claim_ids',[])):w['rows'].add(label+':'+row['row'])
 # Derived rows can select new peer claims absent from the baseline claim list.
 for row in neb['rows']:
  if row.get('composed_status')!='CLOSED':continue
  def strings(x):
   if isinstance(x,str):yield x
   elif isinstance(x,dict):
    for v in x.values():yield from strings(v)
   elif isinstance(x,list):
    for v in x:yield from strings(v)
  for rp in set(strings(row)):
   if rp.startswith('evidence/') and rp.endswith('/receipt.json'):
    w=wanted[rp];w['groups'].add('NEB');w['rows'].add('NEB:'+row['row']);w['claims'].update(row.get('selected_claims',[]))
 for c in nec:
  for rp in c.get('kani_receipt_paths',[])+c.get('control_receipts',[]):
   wanted[rp]['groups'].add('NEC');wanted[rp]['claims'].add(c['claim_id'])
 for group,directory,prefix in [('NEF','slice-q-fnptr-20261029','NEF'),('NEB','slice-q-compose-20261029','NEB'),('NEC','slice-s-leaves-20261029','NEC')]:
  for p in (ROOT/'evidence'/directory).glob(prefix+'_K*/receipt.json'):wanted[str(p.relative_to(ROOT))]['groups'].add(group)
 dirs={ROOT/str(Path(r).parent.parent) for r in wanted};index=collections.defaultdict(list);texts={};manifest={}
 # Include imported merged-slice sources, not only original packet directories.
 dirs.update([ROOT/'evidence/slice-q-compose-20261029',ROOT/'evidence/slice-s-leaves-20261029'])
 seen=set()
 for d in sorted(dirs):
  for p in sorted(d.rglob('*')):
   if not p.is_file() or p in seen:continue
   seen.add(p)
   if not(p.name.endswith(('.rs','.rs.txt','.patch'))):continue
   b=p.read_bytes();name=str(p.relative_to(ROOT));manifest[name]=sha(b)
   if p.name.endswith('.patch'):
    for path,t in patched_files(b.decode(errors='replace')):
     key=name+'::'+path;index[sha(t.encode())].append(key);texts[key]=t
   else:index[sha(b)].append(name);texts[name]=b.decode(errors='replace')
 recovery=E/'NEH_RECOVERED_SOURCES.json.xz'
 if recovery.exists():
  for n,t in read_json(recovery).items():
   key=str(recovery.relative_to(ROOT))+'::'+n;index[sha(t.encode())].append(key);texts[key]=t
 out=[]
 for rp,w in sorted(wanted.items()):
  p=ROOT/rp
  if not p.exists():out.append(dict(receipt=rp,**{k:sorted(v) for k,v in w.items()},harness=None,**classify({},[rp])));continue
  r=read_json(p)
  if r.get('kind') not in ['kani','Kani']:continue
  src={};missing=[];matched={}
  for n,h in r.get('source_hashes',{}).items():
   if not n.endswith(('.rs','.rs.txt')):continue
   candidates=index.get(h,[])
   if candidates:
    key=candidates[0];src[n]=texts[key];matched[n]=dict(sha256=h,source=key);continue
   path=re.search(r'(?:^|/)((?:crates|programs)/.*\.rs)$',n)
   b=frozen(path[1]) if path else None
   if b is not None and sha(b)==h:src[n]=b.decode();matched[n]=dict(sha256=h,source=FROZEN+':'+path[1])
   else:missing.append(dict(source=n,sha256=h))
  ni=r.get('native_command') or r.get('command',[]);harness=r.get('module')
  if '--harness' in ni:harness=ni[ni.index('--harness')+1]
  if not harness:harness=next((v for v in reversed(ni) if '::' in v and not v.startswith('/')),None)
  if not harness:
   for logname in ['stdout.log','stdout.log.xz']:
    q=p.parent/logname
    if q.exists():
     log=(lzma.decompress(q.read_bytes()) if q.suffix=='.xz' else q.read_bytes()).decode(errors='replace')
     mm=re.search(r'Checking harness ([^\s]+?)(?:\.\.\.|[\s])',log)
     if mm:harness=mm[1];break
  out.append(dict(receipt=rp,receipt_sha256=sha(p.read_bytes()),harness=harness,**{k:sorted(v) for k,v in w.items()},matched_sources=matched,**classify(src,missing)))
 result=dict(schema='NEH-applicability-v2',frozen_revision=FROZEN,scope='Receipt-pinned Rust source audit; unresolved inputs suspend credit. NOT-EXPOSED is limited to recorded inputs, not an unrecorded dependency closure.',ndt_active_receipts=len({r for c in ndt['claims'] for r in c.get('active_support_receipts',[])}),counts=dict(collections.Counter(x['classification'] for x in out)),receipts=out)
 (E/'NEH_APPLICABILITY.json').write_text(json.dumps(result,indent=2)+'\n');(E/'NEH_SCAN_INPUTS.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print(json.dumps(dict(counts=result['counts'],receipts=len(out),sources=len(manifest))))
if __name__=='__main__':
 if len(sys.argv)>1:
  p=Path(sys.argv[1]);print(json.dumps(classify({str(p):p.read_text()}),indent=2))
 else:main()
