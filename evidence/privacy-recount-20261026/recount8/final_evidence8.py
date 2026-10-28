from auditlib8 import *
extra=[]
def add_receipt(k,path,stdout=None):
 s=read(k,path)
 if not s:return
 x=json.loads(s);extra.append(dict(ref=k,path=path,target=x.get('module',x.get('target')),exit=x.get('exit',x.get('exit_code')),wall=x.get('wall',x.get('wall_seconds')),peak_RSS=x.get('peak_rss_kib',x.get('peak_rss_kb')),swap=x.get('swap'),source_revision=x.get('source_revision',x.get('revision')),axioms=x.get('print_axioms',x.get('axioms')),qualification='Independent scoped receipt, reused; no new compiler launch'))
 if stdout:read(k,stdout)
for id in ['V234','V235']:
 base='evidence/pv-dlib-20261028/';read('rw',base+'REPORT.txt')
 for name in ['status.json','native-link.json','structural-binding.json']:
  s=read('rw',base+id+'/'+name)
  if name=='native-link.json' and s:
   x=json.loads(s)
   for q in x['kernel_proofs']:add_receipt('rw',base+q['receipt'],base+q['receipt'].replace('receipt.json','output.log'))
   add_receipt('rw',base+id+'/'+x['finite_validation']) if False else None
 add_receipt('rw',base+'wrappers-native-combined-resume4/receipt.json')
add_receipt('rw','evidence/pv-dlib-20261028/lean-43499transport2/receipt.json','evidence/pv-dlib-20261028/lean-43499transport2/output.log')
for path in ['structural132-resume3.json','structural226-resume2.json','features132-resume3.json','closure-hash-audit-resume3.json','receipt-index-resume3.json','receipt-index-resume2.json']:
 read('rw','evidence/pv-b3p6-20261028/'+path)
for p in ['evidence/pv-b3p6-20261028/receipts-resume3/native132-resume3-exact/receipt/receipt.json','evidence/pv-b3p6-20261028/receipts-resume3/lean-51997/receipt/receipt.json','evidence/pv-b3p6-20261028/receipts-resume3/lean-51998/receipt/receipt.json','evidence/pv-b3p6-20261028/receipts-resume3/lean-51999/receipt/receipt.json']:
 add_receipt('rw',p)
 if '/lean-' in p:
  read('rw',p.replace('receipt.json','stdout.log'));read('rw',p.replace('receipt.json','time.log'))
# Independent per-row rdcd evidence, deliberately excluding aggregate-audit credit.
for id in ['V169','V212','V216','V218','V221','V222','V246']:
 j=read('rw','evidence/pv-rdcd-20261028/rows/'+id+'.json') or '';md=read('rw','evidence/pv-rdcd-20261028/rows/'+id+'.md') or ''
 ids=sorted(set(re.findall(r'414\d\d',j+md))-{ '41466','41494','41495','41496','41499'})
 for a in ids:add_receipt('rw','evidence/pv-rdcd-20261028/lean-'+a+'/receipt.json','evidence/pv-rdcd-20261028/lean-'+a+'/output.log')
# Trace the exact Op109 dependency rather than only a prose association.
roots={'V169':'R1Z.PV_RDCD_TakeBinding','V212':'R1Z.PV_CB_Op107Exact','V213':'R1Z.PV_RDCD_Op109Audit','V216':'R1Z.PV_RDCD_ContextInstall','V218':'R1Z.PV_RDCD_Op118Audit','V221':'R1Z.PV_RDCD_Audit','V222':'R1Z.PV_RDCD_Audit','V246':'R1Z.PV_RDCD_StatementBridge'}
cones=[]
for id,root in roots.items():
 paths={root:[root]};todo=[root];missing=[]
 for m in todo:
  if not m.startswith('R1Z.'):continue
  s,p=module('rw',m)
  if s is None:missing.append(m);continue
  for d in re.findall(r'^import\s+(\S+)',s,re.M):
   if d not in paths:paths[d]=paths[m]+[d];todo.append(d)
 cones.append(dict(id=id,root=root,void_binding_import_path=paths.get('R1Z.PV_CB_Op109CanonicalBinding'),unresolved_project_modules=missing))
assert next(x for x in cones if x['id']=='V213')['void_binding_import_path']
assert not any(x['void_binding_import_path'] for x in cones if x['id']!='V213')
(P/'restoration-import-audit8.json').write_text(json.dumps(cones,indent=2)+'\n')
(P/'independent-receipts8.json').write_text(json.dumps(extra,indent=1)+'\n');(P/'manifest.json').write_text(json.dumps(manifest,indent=1)+'\n');print('Independent receipts',len(extra),'import cones',len(cones))
