"""Conservative call-graph support closure; no direct-only promotion."""
from NEK_scan import read_json,sha,ROOT,E
import collections,json,subprocess,lzma,re
from pathlib import Path
_reader=read_json
def bytes_at(path):
 p=Path(path)
 if p.exists():return p.read_bytes()
 return subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(ROOT))])
def read_json(p):
 b=bytes_at(p);return json.loads(lzma.decompress(b) if str(p).endswith('.xz') else b)
all_paths=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],text=True).splitlines()
receipt_paths=collections.defaultdict(list)
for p in all_paths:
 if p.endswith('/receipt.json'):receipt_paths[Path(p).parent.name].append(p)
NEE_DELTA=read_json(ROOT/'evidence/slice-s-compose2-20261029/NEE_LEDGER_DELTA.json')
D=read_json(ROOT/'evidence/slice-q-compose-20261029/NEB_LEDGER.json.xz')
N=read_json(ROOT/'evidence/native-ledger3-20261029/NDT_LEDGER.json')
S=read_json(ROOT/'evidence/slice-s-compose2-20261029/NEE_LEDGER.json.xz')
Q=read_json(ROOT/'evidence/slice-q-compose-20261029/NEB_EDGES.json')
validS=set(read_json(ROOT/'evidence/slice-s-compose2-20261029/NEE_VALIDATION_SUMMARY.json')['slice_closed'])
old=read_json(ROOT/'evidence/k3-audit-20261030/NEH_LEDGER_DELTA.json')
status={r['receipt']:r for r in old['receipts']}
claims={c['claim_id']:c for d in [N,D,S] for c in d['claims']}
for directory in sorted((ROOT/'evidence/slice-q-compose-20261029').glob('NEB_IMPORTED*')):
 p=directory/'NEA_CLOSED.json'
 if not p.exists():continue
 for c in read_json(p):
  q=dict(c);q['active_support_receipts']=[]
  for rp in c.get('kani_receipt_paths',[])+c.get('control_receipts',[]):
   full=directory/rp
   if full.exists():q['active_support_receipts'].append(str(full.relative_to(ROOT)))
   else:
    options=receipt_paths.get(Path(rp).parent.name,[])
    if options:q['active_support_receipts'].extend(options)
  claims[c['claim_id']]=q
byfun=collections.defaultdict(list)
for d in [N,D,S]:
 for r in d['rows']:
  if r not in byfun[r['function']]:byfun[r['function']].append(r)

def strings(x):
 if isinstance(x,str):yield x
 elif isinstance(x,dict):
  for v in x.values():yield from strings(v)
 elif isinstance(x,list):
  for v in x:yield from strings(v)
def receipts(x):return {s for s in strings(x) if s.startswith('evidence/') and s.endswith('/receipt.json')}
def closure(row):
 seen=set();support=set();edges=[];missing=[];cids=set();history=set()
 def visit(r):
  fn=r['function']
  if fn in seen:return
  seen.add(fn)
  selected=r.get('selected_claims',r.get('claim_ids',[]))
  # Receipt pins on the actual row include added root/domain checks.
  replacement=NEE_DELTA['members'].get(fn) if group=='NEE' else None
  if replacement and fn.endswith(('::transfer_common','::withdrawal_common','::digest_is_canonical')):
   history.update(receipts(r.get('receipts',[])));support.update(receipts(replacement))
   selected=[]
  else:
   support.update(receipts(r.get('receipts',[])))
   support.update(receipts(r.get('receipt_sha256',{})))
  # Domain/root certificates can cite native review tables by content hash,
  # rather than listing those native receipts in the ledger row itself.
  certs=[q for q in Q['row_certificates'] if q['function']==fn]
  certs += [q.get('certificate',{}) for q in Q['edges'] if q['caller']==fn and q.get('status')=='CLOSED']
  checked=set()
  def evidence_refs(x):
   support.update(receipts(x))
   if isinstance(x,dict):
    path=x.get('path')
    if isinstance(path,str) and path.endswith('.json') and path not in checked:
     checked.add(path);p=ROOT/path
     if p.exists() or str(p.relative_to(ROOT)) in all_paths:
      if x.get('sha256') and sha(bytes_at(p))!=x['sha256']:missing.append('evidence hash:'+path)
      else:
       data=read_json(p)
       def attempts(y):
        if isinstance(y,dict):
         if isinstance(y.get('attempt'),str) and re.fullmatch(r'[A-Z][A-Za-z0-9_]*_K[0-9]+',y['attempt']):
          if p.name=='receipt.json':support.add(str(p.relative_to(ROOT)))
          else:
           opts=receipt_paths.get(y['attempt'],[]);expected=y.get('receipt_sha256')
           if expected:opts=[q for q in opts if sha(bytes_at(ROOT/q))==expected]
           if not opts:missing.append('receipt ID:'+y['attempt'])
           else:support.update(opts)
         for z in y.values():attempts(z)
        elif isinstance(y,list):
         for z in y:attempts(z)
       attempts(data);evidence_refs(data)
     else:missing.append('review:'+path)
    for v in x.values():evidence_refs(v)
   elif isinstance(x,list):
    for v in x:evidence_refs(v)
  evidence_refs(certs)
  for cid in selected:
   cids.add(cid);c=claims.get(cid)
   if not c:missing.append('claim:'+cid);continue
   support.update(c.get('active_support_receipts',[]))
  for target in r.get('canonical_callees',[]):
   edges.append([fn,target]);choices=byfun.get(target,[])
   if not choices:missing.append('callee:'+target)
   else:
    # Prefer the adopted CLOSED composition instance; fallback retains the
    # strongest recorded local support, never invents closure.
    chosen=next((q for q in choices if q.get('composed_status')=='CLOSED'),choices[0]);visit(chosen)
 visit(row)
 ks=[];lean=[];unknown=[]
 for rp in sorted(support):
  if rp in status:ks.append(dict(receipt=rp,outcome=status[rp]['outcome'],harness=status[rp]['harness']))
  else:
   try:r=read_json(ROOT/rp)
   except FileNotFoundError:unknown.append(rp);continue
   if str(r.get('kind','')).lower()=='kani':ks.append(dict(receipt=rp,outcome='UNREVIEWED',harness=r.get('module')))
   else:lean.append(rp)
 return dict(functions=sorted(seen),edges=edges,claims=sorted(cids),kani=ks,reused_non_kani=lean,historical_references=sorted(history),unresolved=sorted(set(missing+unknown)))
rows=[]
for group,d in [('NEB',D),('NEE',S)]:
 for r in d['rows']:
  if r.get('composed_status')!='CLOSED' or (group=='NEE' and r['row'] not in validS):continue
  c=closure(r);rows.append(dict(row=group+':'+r['row'],function=r['function'],closure=c,fully_cleared=False,limitation='support closure inventory; recovered-input UNAFFECTED does not certify expanded source closure'))
needs=collections.defaultdict(set)
for r in rows:
 for k in r['closure']['kani']:
  if k['outcome'] not in ['RESTORED','UNAFFECTED']:needs[k['receipt']].add(r['row'])
plan=[dict(receipt=rp,dependent_rows=sorted(rs),count=len(rs)) for rp,rs in needs.items()]
plan.sort(key=lambda r:(-r['count'],r['receipt']))
out=dict(schema='NEK-closure-v1',scope='K-3 static/constant sharing; call-structured support closure; no adoption',rows=rows,priority=plan,summary=dict(NEB_rows=sum(r['row'].startswith('NEB:') for r in rows),NEE_rows=sum(r['row'].startswith('NEE:') for r in rows),NEB_fully_cleared=0,NEE_cleared=0))
(E/'NEK_CLOSURE.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out['summary']));print(json.dumps(plan[:18],indent=2))
