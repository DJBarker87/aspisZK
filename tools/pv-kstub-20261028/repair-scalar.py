from pathlib import Path
import json,re,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-kstub-20261028')
p=D/'cb/lib.rs';s=p.read_text();original=(D/'string_scalar-original.rs.txt').read_text()
def function(s,name):
 a=s.index('fn '+name+'(');b=s.index('{',a);i=b+1;d=1
 while d:d+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
s=s.replace(function(s,'string_scalar'),original)
neg=original.replace('fn string_scalar(', 'fn string_scalar_negative(');i=neg.rfind('assert_eq!');neg=neg[:i]+neg[i:].replace('assert_eq!','assert_ne!',1)
s=s.replace(function(s,'string_scalar_negative'),neg);p.write_text(s)
plans=json.loads((D/'plans.json').read_text())
for x in plans:
 if x['harness']=='string_scalar':x['planned_later_body_sha256']=x['body_sha256'];x['body_sha256']=hashlib.sha256(original.encode()).hexdigest();x['restored_historical_body']=True
(D/'plans.json').write_text(json.dumps(plans,indent=2))
(D/'scalar-correction.json').write_text(json.dumps(dict(reason='Historical 131 body uses c.to_string(), later retained source used encode_utf8().to_owned(); restored before scalar verification',body_sha256=hashlib.sha256(original.encode()).hexdigest()),indent=2))
