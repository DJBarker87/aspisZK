from pathlib import Path
import json,hashlib,re,difflib
from RPx_attempt import E,R
rs=[json.loads(f.read_text()) for f in E.glob('RPx_*/receipt.json')]
d=next(d for d in rs if d['module']=='RPx_DeployedAudit' and d['exit_status']==0)
s=(E/d['attempt']/'stdout.log').read_text();name='AspisR1.RPx_Deployed.deployed';histname='AspisR1.FJv_Deployed.deployed'
m=re.search('BEGIN KERNEL TYPE '+re.escape(name)+r'\n(.*?)\nEND KERNEL TYPE '+re.escape(name),s,re.S);assert m
body=m.group(1).strip()+'\n';assert '⋯' not in body and '...' not in body
h=R/'evidence/stack1-20261027/FJv_after_deployed.kernel.lean.txt';historical=h.read_bytes();header='-- Complete kernel type of '+histname+'\n';assert historical.startswith(header.encode())
fresh=header.encode()+body.encode();(E/'RPx_Deployed.kernel.lean.txt').write_bytes(fresh)
sha=lambda b:hashlib.sha256(b).hexdigest()
result=dict(root=name,attempt=d['attempt'],historical_path=str(h.relative_to(R)),historical_sha256=sha(historical),fresh_sha256=sha(fresh),byte_identical=historical==fresh,statement_payload_byte_identical=historical[len(header.encode()):]==body.encode(),complete_no_ellipsis=True,header_note='The historical descriptive comment is preserved for whole-file cmp; it is not part of the kernel statement. Fresh declaration name is RPx_Deployed.deployed. No statement text is normalized.')
(E/'RPx_statement-comparison.json').write_text(json.dumps(result,indent=2)+'\n')
if not result['byte_identical']:
 diff=''.join(difflib.unified_diff(historical.decode().splitlines(True),fresh.decode().splitlines(True),fromfile=str(h),tofile='RPx_Deployed'))
 (E/'RPx_TOP_STATEMENT_DIFFERENCE.diff').write_text(diff);print(diff);raise SystemExit('STOP top statement differs; do not adopt')
print(json.dumps(result,indent=2))
