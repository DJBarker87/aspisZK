"""Check every normalized transparent type module against immutable raw emission."""
from pathlib import Path
import re,json,hashlib,sys
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026';out=[]
for folder,mod in [('types-uint','UInt'),('types-carriers','Carriers'),('types-statement','StatementTypes'),('types-crypto','CryptoTypes'),('types-path','PathTypes'),('types-reserve','ReserveError')]:
 p=e/folder/'Types.lean.txt';raw=p.read_text();s=re.sub(r'(?m)^set_option (maxHeartbeats|maxRecDepth) .*\n','',raw).replace('discriminant isize, ','').replace('@[discriminant isize]\n','')
 if mod=='PathTypes':s=s.replace('inner : Slice Std.U8','inner : Aeneas.Std.Slice Std.U8')
 q=r/f'docs/research/v8-r0-zk-20261009/lean/R1Z/PDict_{mod}Source.lean';assert s==q.read_text(),mod
 assert not re.search(r'(?m)^axiom\b|\bsorry\b|\bnative_decide\b',s)
 out.append(dict(module='R1Z/PDict_'+mod+'Source',raw_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),normalized_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),changes='Only resource-option/discriminant-helper attributes removed; native constructors/fields unchanged; Path Slice name qualified. Enum numeric read/cast laws are not supplied by these type bindings.'))
(e/'type-normalization.json').write_text(json.dumps(out,indent=2)+'\n');print('checked',len(out),'type modules')
