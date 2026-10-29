from pathlib import Path
import json,subprocess,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-owni-20261029';root=R/'docs/research/v8-r0-zk-20261009/lean'
ejr=json.loads(subprocess.check_output(['git','show','HEAD:evidence/envj-rebuild-20261026/EJR_final-inventory.json']))
canon={r['module'].replace('/','.'):r for r in ejr['selected'] if r.get('resolution')}
external={r['module'].replace('/','.') for r in json.loads((R/'evidence/pv-world-20261028/external-object-manifest.json').read_text())}
known={r['module'] for r in json.loads((R/'evidence/pv-ownc-20261029/final-fingerprint.json').read_text())['rows']}
order=[];seen=set();use=[]
def visit(m):
 if m in seen:return
 seen.add(m)
 if m in external or m in known:return
 if m in canon:
  use.append(canon[m]);return
 p=root/(m.replace('.','/')+'.lean')
 if not p.exists():
  aliases={'R1Z.ProverRwFullTypes':'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullTypes.lean','R1Z.ProverRwFullExternalTypes':'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalTypes.lean'}
  assert m in aliases,m
  p=R/aliases[m]
 b=subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))])
 for d in re.findall(r'^import (\S+)',b.decode(),re.M):visit(d)
 order.append(dict(module=m.replace('.','/'),source_path=str(p.relative_to(R)),source_sha256=hashlib.sha256(b).hexdigest(),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip()))
for m in ['R1Z.PV_B2_Total_QM31_mul','R1Z.PV_RDB2D_SparseWeights','R1Z.PV_RDB2D_SparsePublic','R1Z.PV_RDB2D_SparseFieldOrder']:visit(m)
(E/'focused-dependencies.json').write_text(json.dumps(dict(order=order,canonical_ejr=use,rule='h4/h5 precedence; source scan stops at EJR and external authoritative objects'),indent=2)+'\n')
print(len(order),'private dependencies',len(use),'EJR roots');print('\n'.join(r['module'] for r in order))
