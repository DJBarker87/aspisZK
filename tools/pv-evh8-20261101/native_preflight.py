"""Fail-closed census of ExternalFuns aliases hidden in source Result lifts.
This is a static frontier check, never a native coverage certificate.
"""
from pathlib import Path
import hashlib,json,re,subprocess,sys
E=Path('evidence/pv-evh8-20261101')
rev='8b3dc105f492f3a38f1bc9307e5adaf24ad4e5c7'
p='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalFuns.lean'
raw=subprocess.check_output(['git','show',rev+':'+p],text=True)
aliases=dict(re.findall(r'^abbrev (\S+).*? := @ExternalFuns\.(op\d+)\b',raw,re.M))
# Selected source spines currently installed by the opening/nonzero/salts entry.
names=['EntropyStep','NoncePath','SyncDirectory','NonceReserveFallible','NonceReserve',
 'MaterialFromEntropy','ApplyMaterial','BuildSemantics','ProveSemantics','PrivateSalts',
 'PrepareOpening','FinishOpening','PublishCompact','PrivateSaltStep','PrivateSaltsStep','NonzeroStep']
hits=[];records=[]
for n in names:
 ps=[root/(n+'-generation.json') for root in [E,Path('evidence/pv-evh5-20261029')]]
 q=next(p for p in ps if p.exists());x=json.loads(q.read_text())
 records.append(dict(name=n,path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
 for label in x['lifted_calls']:
  if label in aliases:hits.append(dict(spine=n,source_function=x['function'],lifted_callee=label,external_op=aliases[label],status='OPEN native operator/callback/drop association'))
x=dict(status='OPEN; static inventory only',external_source_path=p,external_source_revision=rev,
 external_source_sha256=hashlib.sha256(raw.encode()).hexdigest(),records=records,
 latent_external_lifts=hits,external_ops=sorted({v['external_op'] for v in hits}),
 message='Callee FinishedView hypotheses alone do not establish complete native event coverage. Bind these operators and their reached callbacks/drops, in addition to named Callees and runtime effects.',rows_removed=[])
out=json.dumps(x,indent=2)+'\n';q=E/'native-preflight.json'
if '--check' in sys.argv:assert q.read_text()==out
else:q.write_text(out)
print('Source inventory consistent; native coverage OPEN:',len(hits),'lift sites,',','.join(x['external_ops']))
if '--require-native-closure' in sys.argv and hits:sys.exit(1)
