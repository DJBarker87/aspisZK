from pathlib import Path
import hashlib,json
W=Path(__file__).resolve().parent
M=json.loads((W/'manifest.json').read_text())
assert M['schema']=='focused-extractor-proof-packet-v1'
assert len(M['modules'])==1
mod=M['modules'][0]
for key in ('source','receipt','command','preflight','lean_log','time_log'):
    p=W/mod[key]
    assert p.is_file(), (key,str(p))
assert hashlib.sha256((W/mod['source']).read_bytes()).hexdigest()==mod['source_sha256']
R=json.loads((W/mod['receipt']).read_text())
assert R['exit_status']==0 and R['source_sha256']==mod['source_sha256']
assert R['object_sha256']==mod['object_sha256']
assert R['scope_swap_peak_bytes']==0
P=json.loads((W/mod['preflight']).read_text())
assert P['lean_sha256']==mod['compiler_sha256']
assert P['direct_imports']['S3ActualLoop0Outer12CompositionV1']['sha256']==mod['direct_imports']['S3ActualLoop0Outer12CompositionV1']
print('PASS: focused source-only proof packet')
