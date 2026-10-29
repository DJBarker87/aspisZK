from pathlib import Path
import json,subprocess,hashlib,re,collections
P=Path(__file__).parent;rows=json.loads((P/'credited-row-input.json').read_text());pins=json.loads((P/'input-recount9-pins.json').read_text())['revisions'];refs=list(dict.fromkeys(['bbedfc018d67a8fa6208627e199ee336b628c17e',pins['rw'],pins['b3p6'],pins['rdcd3'],pins['cb'],pins['cb3'],pins['cbmid'],pins['cblib']]))
trees={}
for ref in refs:
 fs=subprocess.check_output(['git','ls-tree','-r','--name-only',ref],text=True).splitlines();d=collections.defaultdict(list)
 for f in fs:
  if f.endswith('.lean'):d[Path(f).stem].append(f)
 trees[ref]=d
out=[];snap=P/'closing-sources';snap.mkdir(exist_ok=True)
for r in rows:
 t=r.get('closure_theorem');res=[]
 if t:
  stem=t.rsplit('.',1)[0].split('.')[-1]
  for ref in refs:
   for path in trees[ref].get(stem,[]):
    data=subprocess.check_output(['git','show',ref+':'+path]);s=data.decode();sha=hashlib.sha256(data).hexdigest();(snap/(sha+'.lean.txt')).write_bytes(data)
    res.append(dict(ref=ref,path=path,sha256=sha,imports=re.findall(r'^\s*(?:public )?import (\S+)',s,re.M),fmt_lines=[dict(line=i,text=l)for i,l in enumerate(s.splitlines(),1)if re.search(r'fmt|Formatter|format!',l)]))
 out.append(dict(id=r['id'],theorem=t,sources=res))
(P/'closing-source-index.json').write_text(json.dumps(out,indent=1));print('located',sum(bool(x['sources'])for x in out),'missing',[x['id']for x in out if not x['sources']]);print('fmt lines',[(x['id'],x['sources'][0]['fmt_lines'])for x in out if x['sources']and x['sources'][0]['fmt_lines']])
