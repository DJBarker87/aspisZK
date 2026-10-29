"""Port exact scalar-root emission by namespace/import metadata only, then
interpret its actual extracted Public.semantic match instead of a hand copy."""
from pathlib import Path
import json,hashlib
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume13';ns='PV_B3P_ScalarSemantic13';rows=[]
for kind in ['Types','Funs']:
 p=O/'semantic-value-root'/(kind+'.lean');s=p.read_text().replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n').replace('import Missing13.Types','import PV_B3P_ScalarSemantic13Types').replace('@[discriminant isize]\n','').replace('PV_B3P_Missing13Semantic-Value-Root13',ns)
 mod='PV_B3P_ScalarSemantic13'+kind;(L/(mod+'.lean')).write_text(s);rows.append(dict(module=mod,raw_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),ported_sha256=hashlib.sha256(s.encode()).hexdigest(),changes=['imports','discriminant metadata','invalid generated namespace punctuation canonicalized consistently'],function_body_edits=[]))
s=(L/'PV_B3P_SemanticBinding13227.lean').read_text().replace('PV_B3P_MissingSemantic13Funs','PV_B3P_ScalarSemantic13Funs').replace('PV_B3P_Missing13Semantic',ns).replace('PV_B3P_Binding13227','PV_B3P_ScalarBinding13227')
a=s.index('def semantic_source13');b=s.index('\ntheorem semantic_source_binding13',a)
s=s[:a]+'''def semantic_source13 (base : ExternalTypes) (p : Public base) : Result SP :=
  letI : ExternalTypes := PV_B3P_Install227.Types base
  let source := match p with
    | .Transfer public1 transition => PV_B3P_ScalarSemantic13.reference_terminal.r0.Public.Transfer (toPrivate public1) (toLate base transition)
    | .Withdrawal public1 transition => PV_B3P_ScalarSemantic13.reference_terminal.r0.Public.Withdrawal (toWithdrawal public1) (toLate base transition)
  do
    let result ← PV_B3P_ScalarSemantic13.reference_terminal.r0.Public.semantic source
    .ok (fromSemantic result)
'''+s[b:]
(L/'PV_B3P_ScalarSemanticBinding13227.lean').write_text(s);(O/'scalar-semantic-port.json').write_text(json.dumps(rows,indent=2)+'\n')
