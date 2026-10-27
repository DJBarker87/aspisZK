from pathlib import Path
import json,re,hashlib,shutil
R=Path(__file__).resolve().parents[2];D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-canon-20261027';records=[]
for p in sorted(D.glob('PV_Canon_*.lean')):
 if p.stem.startswith('PV_Canon_Audit'):continue
 rs=[json.loads(r.read_text()) for r in E.glob('44*/receipt.json') if json.loads(r.read_text()).get('target')=='R1Z/'+p.stem]
 r=max(rs,key=lambda a:a['attempt']) if rs else None
 good=r and r['exit']==0 and r['source_sha256']==hashlib.sha256(p.read_bytes()).hexdigest()
 if not good:
  archive=E/'unsubmitted-drafts'/(p.name+'.txt');archive.parent.mkdir(exist_ok=True);shutil.move(p,archive)
  continue
 names=re.findall(r'\btheorem\s+(\w+)',p.read_text())
 records.append(dict(module=p.stem,source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),attempt=r['attempt'],theorems=names))
B={'Sampler','Polynomial','Semantic','CurrentSemantic','UpdateRead','Prefix','CheckedRound','CheckedRounds','BindCongr','Deployment','Round','RoundCounter','RoundVisit','Result','IndexTotal','ArrayDomain','D234Boundary','D234Impossible'}
C={'RowObligation','FieldMeaning','Horner','HornerMeaning','HornerObligation','QInjective','CanonicalInjective','RowEquivalent','ReachedPolynomial','RadixFour','Limbs','NatMeaning'}
groups={'A':[],'B':[],'Final':[]}
for r in records:
 short=r['module'].removeprefix('PV_Canon_');groups['B' if short in B else 'Final' if short in C else 'A'].append(r)
for g,rows in groups.items():
 imports=['import R1Z.'+r['module'] for r in rows]
 if g=='Final':imports=['import R1Z.PV_Canon_AuditA','import R1Z.PV_Canon_AuditB']+imports
 prints=['#print axioms R1Z.PV_Canon.'+n for r in rows for n in r['theorems']]
 if g=='B':prints+=['#print axioms R1Z.PV_Canon.checked_eval','#print axioms R1Z.PV_Canon.checked_round','#print axioms R1Z.PV_Canon.checked_rounds','#print axioms R1Z.PV_Canon.checked_prover']
 (D/('PV_Canon_Audit'+g+'.lean')).write_text('\n'.join(imports)+'\n\n'+'\n'.join(prints)+'\n')
(E/'audit-manifest.json').write_text(json.dumps(dict(modules=records,groups={g:[r['module'] for r in rs] for g,rs in groups.items()},archived_drafts=[p.name for p in (E/'unsubmitted-drafts').glob('*')]),indent=2)+'\n')
print(len(records),'accepted modules;',sum(len(r['theorems']) for r in records),'theorem reports')
