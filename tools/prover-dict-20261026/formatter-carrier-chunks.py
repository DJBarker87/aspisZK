"""Adapt the checked function-by-function equations to a removed carrier.
Proofs remain individually checked; output generation claims no theorem result.
"""
from pathlib import Path
import re,sys
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'
prior='PDict_FmtCarrierBase'
for suffix in [f'{i:02d}' for i in range(18)]+['17B']+[f'{i:02d}' for i in range(18,26)]:
 if suffix=='17':continue  # The accepted dependency chain uses the17B split.
 source=p/('PDict_FmtErase'+suffix+'.lean');s=source.read_text();s=re.sub(r'import R1Z.PDict_FmtErase\w+','import R1Z.'+prior,s,count=1)
 s=s.replace('namespace R1Z.PDict_FmtErase','namespace R1Z.PDict_FmtCarrier').replace('end R1Z.PDict_FmtErase','end R1Z.PDict_FmtCarrier').replace('variable [ExternalTypes]','')
 s=s.replace('(ops other : ExternalFuns)','(base : ExternalTypes) (ops : @ExternalFuns base)')
 s=re.sub(r'@([\w.]+) _ \(replace ops other\)',r'@\1 (eraseType base) (eraseOps base ops)',s)
 s=re.sub(r'@([\w.]+) _ ops',r'@\1 base ops',s)
 s=re.sub(r'(erase_\d+) ops other',r'\1 base ops',s)
 assert 'replace ops' not in s and 'ops other' not in s,source
 name='PDict_FmtCarrier'+suffix;target=p/(name+'.lean')
 if '--check' in sys.argv:assert target.read_text()==s,target
 else:target.write_text(s)
 prior=name
