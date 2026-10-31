"""Reuse exact source pins, inspect only the dedicated static-free proof crate."""
from pathlib import Path
import json,lzma,hashlib,subprocess,urllib.request
R=Path('evidence/pv-b3p6-20261028/resume17');old=json.loads((R/'std-reached.json').read_text());rows=[];exclusions=[]
for run in ['K73946','K73948','K73950']:
 p=R/(run+'-symbols/index.json')
 if not p.exists():continue
 index=json.loads(p.read_text());found=0
 for record in index['records']:
  if not record['harness']['original_file'].endswith('equivalence_k3_17.rs'):
   exclusions.append(dict(run=run,metadata=record['metadata'],reason='historical different proof crate; not the dedicated static-free configuration'));continue
  found+=1
  f=p.parent/Path(record['symbol_dump']).name;raw=f.read_bytes();assert hashlib.sha256(raw).hexdigest()==record['symbol_dump_sha256']
  table=next(b['symbolTable']for b in json.loads(lzma.decompress(raw))if 'symbolTable'in b)
  assert not any('shared_callee16'in k for k in table)
  for key,v in table.items():
   if v.get('type',{}).get('id')!='code':continue
   loc=v.get('location',{});path=loc.get('file','');name=v.get('prettyName',key)
   if '/library/'not in path:continue
   rel=path.split('/library/',1)[1]
   if not rel.startswith(('core/','std/','alloc/')):continue
   if rel not in old['files']:
    a=R/'std-sources'/rel;a.parent.mkdir(parents=True,exist_ok=True)
    kp=a.with_suffix(a.suffix+'.kani');dp=a.with_suffix(a.suffix+'.deployed')
    url=f"https://raw.githubusercontent.com/rust-lang/rust/{old['compiler_commit']}/library/{rel}"
    if not kp.exists():kp.write_bytes(urllib.request.urlopen(url,timeout=30).read())
    remote='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/'+rel
    if not dp.exists():dp.write_bytes(subprocess.check_output(['ssh','dombarker@100.108.41.90','cat',remote]))
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    old['files'][rel]=dict(kani_source_url=url,kani_source_sha256=sha(kp),deployed_path=remote,deployed_source_sha256=sha(dp),kani_path=str(kp),deployed_capture=str(dp))
   rows.append(dict(group=run,harness=record['harness']['pretty_name'],symbol=key,name=name,location=loc,source=rel,has_body=bool(v.get('prettyValue','')),symbol_dump=str(f),symbol_dump_sha256=record['symbol_dump_sha256']))
 assert found,run
x=dict(old,rows=rows,method='Dedicated K-3 harness original_file selected from same-scope exact symbol capture; complete code-typed item set; historical other proof crates excluded with reasons',excluded_records=exclusions)
(R/'K3-STD-REACHED.json').write_text(json.dumps(x,indent=2)+'\n')
s=Path('tools/pv-b3p6-20261028/std_compare227_resume17.py').read_text().replace("D/'std-reached.json'","D/'K3-STD-REACHED.json'").replace("D/'STD-PARITY.json'","D/'K3-STD-PARITY.json'")
exec(compile(s,'std_compare227_resume17.py','exec'))
