import subprocess,pathlib,json,re,lzma,hashlib,collections
E=pathlib.Path(__file__).resolve().parent
pins=json.loads((E/'PINS.json').read_text())['pins']
refs=['codex/pv-runjoin-20261026','codex/pv-rdcd4-20261029','codex/pv-b3p6-20261028','codex/pv-cblib-20261027','codex/pv-l2b-20261027','codex/pv-l2c-20261028','codex/pv-gate6-20261028','codex/cx-prover-rw-20261023']
rows=[];seen=set();trees={};blobs=E/'blobs';blobs.mkdir(exist_ok=True)
def get(rev,p):
 r=subprocess.run(['git','show',rev+':'+p],capture_output=True);return r.stdout if r.returncode==0 else None
def strings(x):
 if isinstance(x,str):yield x
 elif isinstance(x,dict):
  for v in x.values():yield from strings(v)
 elif isinstance(x,list):
  for v in x:yield from strings(v)
for ref in refs:
 rev=pins.get(ref) or subprocess.check_output(['git','rev-parse',ref]).decode().strip()
 ns=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'evidence/','tools/']).decode().splitlines();trees[ref]={'revision':rev,'files':ns}
 candidates=[p for p in ns if p.startswith('evidence/pv-') and p.endswith(('receipt.json','receipts.json')) and re.search('kani|/K[0-9]|/k[0-9]',p,re.I)]
 for p in candidates:
  b=get(rev,p)
  if not b:continue
  sha=hashlib.sha256(b).hexdigest()
  if (p,sha) in seen:continue
  seen.add((p,sha))
  try:d=json.loads(b)
  except:continue
  s=' '.join(strings(d))
  if not re.search(r'\bcargo\s+kani\b|\bkani\b',s):continue
  (blobs/(sha+'.json')).write_bytes(b)
  rows.append(dict(branch=ref,revision=rev,path=p,sha256=sha,receipt=d))
 print(ref,'total receipts',len(rows),flush=True)
(E/'RECEIPTS.json').write_text(json.dumps(rows,indent=2)+'\n')
# No need to persist giant duplicated file trees; per-reference only tool/source metadata selected later.
(E/'SOURCE_PATHS.json').write_text(json.dumps({r:{'revision':v['revision'],'files':[p for p in v['files'] if p.startswith('tools/pv-') and p.endswith(('.rs','.rs.txt','.patch','.py'))]} for r,v in trees.items()},indent=2)+'\n')
print('done',len(rows))
