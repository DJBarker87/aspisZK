#!/usr/bin/env python3
from pathlib import Path
import subprocess,hashlib,json,re
R=Path(__file__).resolve().parents[2];rev='b2727acd3abf79315d18b754a260f58f4b1c6326';s=subprocess.check_output(['git','-C',str(R),'show',rev+':crates/aspis-r1-cost-probe/src/verifier.rs'],text=True)
def cut(s):
 a=s.index('fn prepared_claim<');e=s.index('{',a)+1;d=1
 while d:d+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[a:e]
expected=cut(s)
code='''from pathlib import Path
import json,hashlib
r=Path('/home/dombarker/project-offloads/s1-current-claim-extraction-v2-20261020');s=(r/'input/lib.rs').read_text();a=s.index('fn prepared_claim<');e=s.index('{',a)+1;d=1
while d:d+=(s[e]=='{')-(s[e]=='}');e+=1
p=r/'CurrentPowers.llbc';x=json.loads(p.read_text())
print(json.dumps(dict(body=s[a:e],lib_sha256=hashlib.sha256((r/'input/lib.rs').read_bytes()).hexdigest(),llbc_path=str(p),llbc_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),has_errors=x['has_errors'])))
'''
remote=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True));remote.update(freeze=rev,source_path='crates/aspis-r1-cost-probe/src/verifier.rs',frozen_body=expected,whitespace_erased_body_equal=re.sub(r'\s+','',expected)==re.sub(r'\s+','',remote['body']),qualification='Exact original nested claim body in retained source cut, modulo whitespace. Carrier/child bindings still require their reviewed source inventories; reusing LLBC does not close those gates.')
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021';(E/'original-claim-cache-pin.json').write_text(json.dumps(remote,indent=2)+'\n');assert remote['whitespace_erased_body_equal'] and not remote['has_errors'];print('PASS retained original-claim body equality and valid LLBC')
