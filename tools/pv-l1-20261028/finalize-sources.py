import pathlib,json,re,hashlib
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-l1-20261028';D=R/'docs/research/v8-r0-zk-20261009/lean'
rs=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]; accepted={r['target']:r for r in rs if r['accepted'] and r['target'].startswith('PV_L1_')}
names=[]
for m,r in sorted(accepted.items()):
 assert hashlib.sha256((D/(m+'.lean')).read_bytes()).hexdigest()==r['source_sha256']
 names.extend(re.match(r"'([^']+)'",s)[1] for s in r['axioms'])
names=sorted(set(names));assert names and all(n.startswith('PV_L1_') for n in names)
(E/'accepted-theorems.json').write_text(json.dumps(dict(modules=sorted(accepted),theorems=names),indent=2)+'\n')
(D/'PV_L1_Audit.lean').write_text('\n'.join('import '+m for m in sorted(accepted))+'\n-- Accepted emission/model lemmas only; no deployed native claim.\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
core=[n for n in names if any(n.startswith(m+'.') for m in ['PV_L1_CanonicalSource','PV_L1_QueryRecord','PV_L1_EntropyProducer','PV_L1_EntropyCounts','PV_L1_SamplerJoint','PV_L1_QueryProducer','PV_L1_NativeProducer'])]
(D/'PV_L1_Statements.lean').write_text('import PV_L1_Audit\n'+'\n'.join('#print '+n for n in core)+'\n')
(D/'PV_L1_FocusedReplay.lean').write_text('import PV_L1_Audit\nimport PV_L1_Statements\n-- One final focused replay; not a frozen privacy-endpoint release replay.\n'+'\n'.join('#print axioms '+n for n in core)+'\n')
drafts=[];(E/'drafts').mkdir(exist_ok=True)
for p in D.glob('PV_L1_*.lean'):
 if p.stem in accepted or p.stem in ['PV_L1_Audit','PV_L1_Statements','PV_L1_FocusedReplay']:continue
 dest=E/'drafts'/(p.name+'.txt');dest.write_bytes(p.read_bytes());p.unlink();drafts.append(dict(module=p.stem,sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),status='unaccepted draft; not imported in audit'))
(E/'draft-status.json').write_text(json.dumps(drafts,indent=2)+'\n')
print(len(accepted),len(names),len(drafts))
