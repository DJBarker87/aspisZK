"""Read-only h7 resolution diagnostics; never substitute missing cohort objects."""
import json,subprocess,hashlib,shlex
from pathlib import Path
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin35-20261028'
rev=subprocess.check_output(['git','rev-parse','research'],text=True).strip()
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
def read(p):return subprocess.check_output(['git','show',rev+':'+p])
base='docs/research/100bit-spend-path-20261013/evidence/import-union-20261022/'
graph=json.loads(read(base+'host-module-graph.json'));pins={r['module']:r for r in json.loads(read(base+'build-host/raw-object-pins.json'))}
old=json.loads((R/'evidence/pv-runjoin34-20261028/oracle-source-ambiguities.json').read_text())
external={r['module'].replace('/','.'):r for r in json.loads((E/'external-authority.json').read_text())}
rows=[]
for v in old['unresolved']:
 m=v['module'];r=dict(module=m,variants=v['variants'],consumers=v['consumers'],graph_entry=graph.get(m))
 if m=='R1PublicCodecAgreement':
  inv=json.loads(read('evidence/envj-rebuild-20261026/EJR_final-inventory.json'))
  a=[v for v in inv['selected'] if (v.get('resolution') or {}).get('path','').endswith('/R1PublicCodecAgreement.lean')]
  assert len(a)==1;a=a[0];b=subprocess.check_output(['git','cat-file','blob',a['resolution']['blob']]);assert hashlib.sha256(b).hexdigest()==a['sha256']
  r.update(status='resolved EJR under h5 prime',ejr_record=a,module_alias='PublicCodecAgreement -> R1PublicCodecAgreement (resolution basename)',source_sha256=a['sha256'])
 elif m in graph:
  seen=set();closure=[]
  def walk(n):
   if n in seen:return
   seen.add(n)
   if n not in pins:closure.append(dict(module=n,status='missing raw object pin'));return
   p=pins[n];closure.append(dict(module=n,path=p['selected_path'],resolved_path=p['resolved_path'],sha256=p['sha256'],current_external_sha256=external.get(n,{}).get('object_sha256')))
   for d in p['imports']:walk(d)
  walk(m)
  code='''import json,sys,pathlib,hashlib
x=json.load(sys.stdin)
for r in x:
 for key in ['path','resolved_path']:
  if key in r:
   q=pathlib.Path(r[key]);r[key+'_exists']=q.is_file();r[key+'_actual_sha256']=hashlib.sha256(q.read_bytes()).hexdigest() if q.is_file() else None
print(json.dumps(x))'''
  t=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(closure),text=True,capture_output=True);assert t.returncode==0,t.stderr
  c=json.loads(t.stdout);r.update(object_pin=pins[m],cohort_closure=c,status='cohort gap: recorded object absent; h6 reuse not admissible',fallback='no importer-generation hash chain established; tracked alternatives are not authority')
 else:
  p='docs/research/100bit-spend-path-20261013/evidence/withdrawal-validation-source-431-20261015/manifest.json';x=json.loads(read(p));imp=json.loads((R/'evidence/pv-runjoin34-20261028/oracle34-resolution.json').read_text())['resolved']['WithdrawalValidationAmount431'];assert imp['sha256']==x['checked_modules']['WithdrawalValidationAmount431']['source_sha256'];ap=p.rsplit('/',1)[0]+'/extraction/attempt-c-fixed-digest/artifact-pins.json';ab=read(ap);art=json.loads(ab);variant=p.rsplit('/',1)[0]+'/extraction/attempt-c-fixed-digest/generated/AspisR1WithdrawalValidation/Funs.lean';vb=read(variant);assert hashlib.sha256(vb).hexdigest()==art['generated/AspisR1WithdrawalValidation/Funs.lean']==x['checked_modules'][m]['source_sha256'];r.update(status='resolved h7 generation receipt hash chain',importer_resolution=imp,artifact_pins_path=ap,artifact_pins_sha256=hashlib.sha256(ab).hexdigest(),source_path=variant,source_sha256=hashlib.sha256(vb).hexdigest(),manifest=p,manifest_sha256=hashlib.sha256(read(p)).hexdigest(),checked_modules=x['checked_modules'])
 rows.append(r)
(E/'h7-resolution.json').write_text(json.dumps(dict(head=head,research_revision=rev,graph_path=base+'host-module-graph.json',graph_sha256=hashlib.sha256(read(base+'host-module-graph.json')).hexdigest(),rows=rows,import_allowed=False,action='no oracle cone imported; continue independent source worker/merge laws'),indent=2)+'\n')
for r in rows:print(r['module'],r['status'])
