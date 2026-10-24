"""Reject a zero-inclusive near-match of the sole supported scalar pattern."""
from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent
j=json.loads((D/'ProverRwRngExtractorsynthetic.llbc').read_text())
p=j['translated']['type_decls'][6]['kind']['Struct'][0]['ty']['HashConsedValue'][1]['Pattern'][1]['OrPattern']
bound=p[1]['Range'][0]['kind']['Literal']['Scalar']['Signed'];assert bound==['I32','1'];bound[1]='0'
out=D/'ProverRwRngExtractorpattern009.llbc';out.write_text(json.dumps(j,separators=(',',':'))+'\n')
