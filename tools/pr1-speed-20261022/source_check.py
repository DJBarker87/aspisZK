#!/usr/bin/env python3
"""Bind the stage-1 per-step gate to the exact baseline and changed callers."""
from pathlib import Path
import subprocess,re,hashlib,json
r=Path(__file__).resolve().parents[2]
base='4209a51d40a59a285601db28a3122a01f84e9510'
z='docs/research/v8-r0-zk-20261009/z4/'
def old(p):return subprocess.check_output(['git','show',base+':'+p],cwd=r,text=True)
def function(s,name):
 a=s.index('fn '+name+'(');a=s.index('{',a);depth=1;b=a+1
 while depth:depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b]
old_d=old(z+'z9d.rs');new_d=(r/(z+'z9d.rs')).read_text();old_e=old(z+'z9e.rs');new_e=(r/(z+'z9e.rs')).read_text()
assert function(old_d,'family')==function(new_d,'family')
assert function(old_d,'convert')==function(new_d,'convert_shared').replace('Some((pb, cc, fq.sid, fg.sid))','Some((pb, cc))')
assert function(old_e,'public_data')==function(new_e,'public_data')
closure_start=old_e.index('    let desc = |f: &Fam|');start=old_e.index('{',closure_start);depth=1;end=start+1
while depth:depth+=(old_e[end]=='{')-(old_e[end]=='}');end+=1
old_projection=old_e[start:end].replace('f.sid','sid')
reference=function((r/'tools/pr1-speed-20261022/gates.rs').read_text(),'reference')
assert re.sub(r'\s+','',old_projection)==re.sub(r'\s+','',reference)

assert function(old_e,'p_r1_check')==function(new_e,'p_r1_check').replace('let (mut pb, cc, sidq, sidg) = convert_shared(&p, &cert, &ln)?;','let (mut pb, cc) = convert(&p, &cert, &ln)?;').replace('extracted_builders_shared(&p, &cert, &sidq, &sidg, &mut pb)?;','extracted_builders(&p, &cert, &ln, &mut pb)?;')
fills=lambda s:re.findall(r'aspis_r1_cert_build::\w+\([^;]+;',s)
assert fills(function(old_e,'extracted_builders'))==fills(function(new_e,'extracted_builders_shared'))
for path in ['docs/research/v8-r0-zk-20261009/c3/check/src/lib.rs','docs/research/v8-r0-zk-20261009/c3/build/src/lib.rs']:
 assert old(path)==(r/path).read_text()
for p in ['gates.rs','../../docs/research/v8-r0-zk-20261009/z4/source_descriptors.rs']:
 assert (Path(__file__).parent/p).exists()
print(json.dumps({'baseline':base,'passed':['family unchanged','all converter arithmetic and checks retained','public_data unchanged','Kani reference is the exact old projection','p_r1_check only changes descriptor handoff','all extracted fill calls identical','extracted checker and builder arithmetic unchanged'],'source_sha256':{p:hashlib.sha256((r/p).read_bytes()).hexdigest() for p in [z+'z9d.rs',z+'z9e.rs',z+'source_descriptors.rs','tools/pr1-speed-20261022/gates.rs']}},indent=2))
