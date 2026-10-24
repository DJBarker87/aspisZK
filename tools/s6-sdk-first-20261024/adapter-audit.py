#!/usr/bin/env python3
"""Audit complete selected adapter sources before mixing any caller proof."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s6-sdk-first-20261024';P.mkdir(exist_ok=True);rev='97caa13d92'
sha=lambda b:hashlib.sha256(b).hexdigest();rows=[]
def root(n):return subprocess.check_output(['git','-C',str(R),'show',rev+':'+str((B/'lean'/(n+'.lean')).relative_to(R))])
for n,attempt in [('AdapterRwTypes','s6-current-adapter-original-module-types-v1'),('AdapterRwModel','s6-current-adapter-original-module-model-v1'),('AdapterRwCuts','s6-current-adapter-original-module-cuts-v1')]:
 a=(E/attempt/'source.lean').read_bytes();b=root(n);s=a.decode()
 if n=='AdapterRwTypes':s=s.replace('S6CurrentNamedDiscriminantV1','ImportUnionNamedDiscriminant').replace('s6_current_discriminant','import_union_discriminant')
 if n=='AdapterRwTypes':s=s.replace('\n#print axioms AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1\n','\n')
 if n=='AdapterRwModel':s=s.replace('\n#print axioms AdapterRw.Ops\n','\n')
 assert s.strip()==b.decode().strip(),n
 rows.append(dict(module=n,selected_snapshot=str((E/attempt/'source.lean').relative_to(R)),selected_sha256=sha(a),research_revision=rev,research_path=str((B/'lean'/(n+'.lean')).relative_to(R)),research_sha256=sha(b),normalization_equal=True))
a=(B/'lean-candidates/s126-caller-boundary-20261021/S6CurrentNamedDiscriminantV1.lean').read_text();b=root('ImportUnionNamedDiscriminant').decode()
for x,y in [('AspisS6CurrentNamedDiscriminant','ImportUnionNamedDiscriminant'),('s6CurrentDiscriminantAttribute','namedDiscriminantAttribute'),('s6CurrentDiscriminant','namedDiscriminant'),('s6_current_discriminant','import_union_discriminant')]:a=a.replace(x,y)
a=re.sub(r'^#print axioms .*\n?','',a,flags=re.M);assert a.strip()==b.strip()
(P/'adapter-source-compatibility.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',modules=rows,macro_normalization_equal=True,macro_rule='Only attribute/elaborator namespace names differ; the command generator, enum-qualified reader/instance names and entire callback body are identical.',scope='Complete adapter definitions and generator source audit. No source operation/type/field/constructor changed. Does not certify an entire mixed object closure or frozen artifact.'),indent=2)+'\n')
print(json.dumps(dict(status='PASS',modules=len(rows),macro_equal=True)))
