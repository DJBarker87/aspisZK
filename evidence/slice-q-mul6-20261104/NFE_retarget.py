from pathlib import Path
import json,subprocess,hashlib,re
E=Path(__file__).resolve().parent
x=json.loads((E/'NFE_INVENTORY.json').read_text());used=x['used'];rt=x['retarget'];sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
read=lambda p:subprocess.check_output(['git','show','HEAD:'+p],text=True)
rows=[]
for m,rp in rt.items():
 p='evidence/replay-tops1-20261027/'+rp+'.lean';s=read(used[m]['path']);t=read(p)
 body=lambda s:'\n'.join(l for l in s.splitlines() if not l.startswith('import '))
 assert body(s)==body(t),m
 refs=sorted(set(n for r in used.values() for n in re.findall(r'\b'+re.escape(m)+r'\.[\w.]+',read(r['path']))))
 rows.append(dict(original=m,headline=rp,original_path=used[m]['path'],headline_path=p,original_sha256=sha(s),headline_sha256=sha(t),nonimport_body_sha256=sha(body(s)),declarations_identical=True,used_declarations=refs,carrier_relation='Identical declarations in identical namespace; no carrier substitution. Only transitive import-owner retargeting.'))
a=set(rt)
while True:
 b=a|{m for m,r in used.items() if a.intersection(r['imports'])}
 if a==b:break
 a=b
mapping={m:'NFE_'+m for m in sorted(a-set(rt))};replacements={**rt,**mapping}
# Namespaces and references of copied consumers move together; RPt declarations retain old names.
pattern=re.compile('|'.join(re.escape(n) for n in sorted(mapping,key=len,reverse=True)))
provenance=[]
for m,n in mapping.items():
 s=read(used[m]['path']);t=pattern.sub(lambda z:mapping[z.group()],s)
 t='\n'.join(('import '+' '.join(rt.get(k,k) for k in l[7:].split())) if l.startswith('import ') else l for l in t.splitlines())+'\n'
 (E/(n+'.lean')).write_text(t)
 provenance.append(dict(original_module=m,new_module=n,source=used[m]['path'],source_sha256=sha(s),destination_sha256=sha(t)))
order=[];seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 for d in used[m]['imports']:
  if d in mapping:visit(d)
 order.append(mapping[m])
for m in mapping:visit(m)
(E/'NFE_BUILD_ORDER.json').write_text(json.dumps(order,indent=2)+'\n')
(E/'NFE_RETARGET.json').write_text(json.dumps(dict(schema='NFE-retarget-v1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),cohort='NER_STREAM_B_COHORT.jsonl.xz',relations=rows,provenance=provenance,modules=len(mapping),pending='NER source/object pin verification and focused elaboration'),indent=2)+'\n')
print(len(mapping),'new consumer modules;',len(rows),'identical declaration relations')
