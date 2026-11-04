"""Validate the complete C lift campaign from terminal raw receipts."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
rows=[]
for n in range(38,58):
 a=f'NFV_K{n:03}';rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 shape=json.loads((E/(a+'-shape.json')).read_text());negative=(n%2==1 or n>=56)
 assert rc['exit_status']==int(negative),(a,rc['exit_status'])
 assert 'timed out' not in out.lower() and 'unwinding assertion' not in out,(a,'no-credit terminal')
 assert ('assertion failed:' in out) if negative else ('VERIFICATION:- SUCCESSFUL' in out or 'VERIFICATION:- SUCCESSFUL'.replace(':-',':') in out or 'VERIFICATION RESULT' in out),a
 if n==56:assert 'core::ptr::eq(instruction, self.instruction)' in out
 if n==57:assert 'infos.len() == 8 && core::ptr::eq(infos.as_ptr().cast::<()>(), self.infos)' in out
 assert rc['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 graph=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text());rule=json.loads((E/(a+'-rule16-check.json')).read_text())
 assert graph['graph_matches_frozen'] and graph['exact_LPm_graph']
 assert rule['no_writable_static'];assert rc['swaps']=='0'
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 rows.append(dict(attempt=a,mode=shape['mode'],exit=rc['exit_status'],wall=rc['wall_seconds'],peak_rss_kib=rc['peak_rss_kib'],swap=rc['swaps'],receipt_sha256=hashlib.sha256((E/a/'receipt.json').read_bytes()).hexdigest(),lock=lock))
(E/'NFV_C_LIFTS.json').write_text(json.dumps(dict(status='controlled native post-admission cuts; not complete process-prefix association',returned_domain='capacity=len=792; SAME getter object, returned bytes and decoded value; seven metas,320request bytes,eight AccountInfos, SAME borrowed Instruction and info-array addresses',account_data_caveat='fixtures have empty input account-data; the cut only forwards the borrowed info slice unchanged and does not inspect its contents; production data/roles and every child PacketDomain still require B',K051_excluded=True,rows=rows),indent=1)+'\n')
print(len(rows),'terminal C receipts checked')
