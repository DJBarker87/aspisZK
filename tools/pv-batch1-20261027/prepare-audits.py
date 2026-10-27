from pathlib import Path
import re,json,hashlib
E=Path('evidence/pv-batch1-20261027');D=E/'lean'
modules=sorted(p.stem for p in D.glob('PV_B1_*.lean') if 'Audit' not in p.stem)
def queries(module):
 s=(D/(module+'.lean')).read_text();ns=re.findall(r'^namespace (\S+)',s,re.M)
 names=re.findall(r'^#print axioms (\S+)',s,re.M)
 return [((ns[0]+'.') if ns else '')+n for n in names]
groups=[('PV_B1_AuditSource',['PV_B1_SumOriginal','PV_B1_PowersBridge','PV_B1_PoleBridge','PV_B1_MaskShift','PV_B1_MaskCast','PV_B1_Shift31','PV_B1_Orig258_Op258RowLaw']),('PV_B1_AuditTyped',['PV_B1_SelectedContract','PV_B1_ReferenceInstall','PV_B1_HostSumSource','PV_B1_HostPoleTruth','PV_B1_CarrierResultRecovery','PV_B1_HostFailureIndependence']),('PV_B1_AuditManifest',modules)]
rows=[]
for name,imports in groups:
 names=[q for m in imports for q in queries(m)]
 s='\n'.join('import '+m for m in imports)+'\nopen Aeneas Aeneas.Std\n-- Frozen dependency closure and standard-axiom audit only.\n'+'\n'.join('#print axioms '+q for q in names)+'\n'
 (D/(name+'.lean')).write_text(s)
 rows.append(dict(module=name,imports=imports,axiom_queries=names,sha256=hashlib.sha256(s.encode()).hexdigest()))
(E/'audit-manifest.json').write_text(json.dumps(dict(source_modules={m:hashlib.sha256((D/(m+'.lean')).read_bytes()).hexdigest() for m in modules},audits=rows),indent=2)+'\n')
print([(r['module'],len(r['imports']),len(r['axiom_queries'])) for r in rows])
