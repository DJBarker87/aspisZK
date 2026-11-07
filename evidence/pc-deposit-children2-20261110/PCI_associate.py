from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
r=next(r for r in json.loads((E/'PCI_SOURCE_MAP.json').read_text()) if r['id']=='POOL:332')
f=r['frozen_function'];s=(E/'PCI_CountNative.rs').read_text();a=s.index('fn require_exact_account_count_fission');b=s.index('\n// Retired whole-ProgramError',a);copy=s[a:b].strip();fb=f[f.index('{'):];cb=copy[copy.index('{'):];norm=lambda x:re.sub(r'\s+','',x)
def check(c):return norm(c.replace('len','accounts.len()'))==norm(fb)
assert check(cb)
assert not check(cb.replace('< expected','<= expected'))
assert not check(cb.replace('InvalidArgument','NotEnoughAccountKeys'))
x=[dict(row='POOL:332',frozen_full_function_sha256=r['full_function_sha256'],frozen_body_sha256=r['frozen_body_sha256'],fission_sha256=hashlib.sha256(copy.encode()).hexdigest(),transforms=[['len','accounts.len()']],body_exact_after_whitespace=True,mutation_controls=['comparison corruption rejected','error arm corruption rejected'],classification='ReviewedTranscription option A; no trust removed')]
(E/'PCI_ASSOCIATIONS.json').write_text(json.dumps(x,indent=1)+'\n')
print('PCI332 exact body and both mutation controls verified')
