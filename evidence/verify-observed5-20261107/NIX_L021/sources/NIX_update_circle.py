from pathlib import Path
import json,hashlib,re
B=Path(__file__).resolve().parent;S=B/'NIX_src';n='crates/aspis-core/src/circle.rs';p=S/n;s=p.read_text();start=s.index('#[cfg(kani)]\nmod NIX_circle');original=s[:start];new=(B/'NIX_circle.rs.txt').read_text();p.write_text(original+new)
x=json.loads((B/'NIX_SOURCE_PINS.json').read_text());x[n]=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NIX_SOURCE_PINS.json').write_text(json.dumps(x))
# Independently reconstruct the native map cut from the frozen function, preserving evaluation nesting.
m=re.search(r'pub fn secure_circle_point_from_parameter\([\s\S]*?\) -> Result<SecureCirclePoint, CirclePointError> \{([\s\S]*?)\n\}',original);raw=m[1];changed=raw
repls=json.loads((B/'NIX_MAP_REPLACEMENTS.json').read_text())
for old,replacement in repls:assert changed.count(old)==1;changed=changed.replace(old,replacement)
actual=new.split('fn map_step(',1)[1].split('Result<SecureCirclePoint,CirclePointError>{',1)[1].split('\n }\n #[kani::proof]',1)[0]
assert actual==changed
norm=lambda s:re.sub(r'\s+','',re.sub(r'//[^\n]*','',s))
step=new.split('fn step(',1)[1].split('Result<SecureCirclePoint,CirclePointError>{',1)[1].split('\n }',1)[0].replace('oracle(parameter,log)','secure_circle_point_from_parameter(parameter)')
m=re.search(r'pub fn secure_ood_circle_point_from_parameter\([\s\S]*?\) -> Result<SecureCirclePoint, CirclePointError> \{([\s\S]*?)\n\}',original)
assert norm(step)==norm(m[1])
(B/'NIX_CIRCLE_ERASURE.json').write_text(json.dumps(dict(ood_token_erasure=True,map_exact_body_replacement=True,frozen_map_sha256=hashlib.sha256(raw.encode()).hexdigest(),new_cut_sha256=hashlib.sha256(actual.encode()).hexdigest(),replacements=repls,product_execution='NONE; local-record opaque call logs'),indent=2));print('NIX circle exact replacement/erasure validated')
