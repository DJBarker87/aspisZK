from pathlib import Path
import hashlib,json,re,sys
b=Path.cwd();a=sys.argv[1];x=json.loads((b/'PCC_CURRENT_INPUTS.json').read_text());out=[]
for module,record in x['modules'].items():
 p=b/record['source'];raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==record['sha256'],module
 code=re.sub(r'/\-.*?\-/','',raw.decode(),flags=re.S);code=re.sub(r'--[^\n]*','',code)
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+(maxRecDepth|maxHeartbeats)',code,re.M),module
 obj=b/'PCC_objects'/(module+'.olean');assert obj.exists(),module
 out.append(dict(module=module,source_sha256=record['sha256'],compile_attempt=record['compile_attempt'],object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest()))
assert all(c['match'] for c in x['frozen_source'])
(b/(a+'-source-review.json')).write_text(json.dumps(dict(status='PASS_SUPPORT_INPUTS_ONLY',modules=out,forbidden_constructs=0,pool_rows_closed=0),indent=1)+'\n')
print('Current support sources match successful hashes; frozen pins and static discipline pass')
