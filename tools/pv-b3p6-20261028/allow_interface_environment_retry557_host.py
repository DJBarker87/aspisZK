"""Record the one u-prime retry after the namespace-completeness repair."""
from run import H
import json,hashlib
failed=H/'lean-79726/receipt/receipt.json';fixed=H/'lean-79728/receipt/receipt.json'
f=json.loads(failed.read_text());r=json.loads(fixed.read_text());assert f['exit_status']!=0 and r['exit_status']==0
assert r['module']=='R1Z.ProverRwFullFuns'
obj=H/'lean-objects/R1Z/ProverRwFullFuns.olean'
row=dict(module=f['module'],source_sha256=f['source_sha256'],failed_receipt_sha256=hashlib.sha256(failed.read_bytes()).hexdigest(),failed_attempt=79726,corrected_receipt=str(fixed),corrected_source_sha256=r['source_sha256'],corrected_dependency=dict(module=r['module'],path=str(obj),object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest()),ruling='u-prime + h6-prime; missing private-namespace object fixed; exact original source retained')
(H/'resume18/environment-exceptions-D557.json').write_text(json.dumps([row],indent=2)+'\n');print('one pinned environment exception recorded')
