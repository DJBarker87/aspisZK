from pathlib import Path
import json,sys
sys.dont_write_bytecode=True
from NHC_validate import validate
E=Path(__file__).resolve().parent
checks=[]
def mutate(label,path,fn):
 raw=(E/path).read_bytes();value=json.loads(raw);fn(value)
 try:validate({path:json.dumps(value).encode()})
 except (AssertionError,KeyError,ValueError):checks.append(dict(mutation=label,rejected=True));return
 raise AssertionError('mutation accepted: '+label)
mutate('false admission allowed with exit zero','NHC_K010-admission.json',lambda x:x['reservation'].update(allowed=False))
mutate('refused admission exit','NHC_K010-admission.json',lambda x:x.update(exit=78))
mutate('swap permitted','NHC_K010/receipt.json',lambda x:x['limits'].update({'memory.swap.max':'1'}))
mutate('memory cap changed','NHC_K010/receipt.json',lambda x:x['limits'].update({'memory.max':'17179869184'}))
mutate('frozen dependency drift','NHC_K010-graph-check.json',lambda x:x.update(exact_LPm_graph=False))
mutate('post lock drift','NHC_K010-lock-check.json',lambda x:x.update(after='0'*64))
mutate('writable static','NHC_K010-rule16-check.json',lambda x:x.update(no_writable_static=False))
mutate('wrong copy patch','NHC_K010.json',lambda x:x.update(copy_patch_sha256='0'*64))
mutate('unproved helper model','NHC_LOADER_CERTIFICATE.json',lambda x:x.update(theorem='NHC_Missing.result'))
mutate('restricted owner domain','NHC_LOADER_CERTIFICATE.json',lambda x:x.update(domain='one owner'))
mutate('uncertified modifies set','NHC_LOADER_CERTIFICATE.json',lambda x:x.update(modifies=['account data']))
mutate('wrong native target','NHC_LOADER_CERTIFICATE.json',lambda x:x.update(function='different::supported_loader'))
mutate('changed inherited reference','NHC_LOADER_CERTIFICATE.json',lambda x:x.update(reference_sha256='0'*64))
mutate('raw nonstandard axiom','NHC_AUDIT.json',lambda x:x.update(standard_only=False))
mutate('incoherent forest','NHC_AUDIT.json',lambda x:x['scan'].update(incompatible_owners=1))
mutate('changed retarget proof bytes','NHC_PROVENANCE.json',lambda x:x['files'][0].update(target_sha256='0'*64))
for label,path,old,new in [('forged native pass','NHC_K010/stdout.log',b'VERIFICATION:- SUCCESSFUL',b'VERIFICATION:- FAILED'),('nonfailing native control','NHC_K011/stdout.log',b'VERIFICATION:- FAILED',b'VERIFICATION:- SUCCESSFUL')]:
 raw=(E/path).read_bytes();assert old in raw
 try:validate({path:raw.replace(old,new)})
 except AssertionError:checks.append(dict(mutation=label,rejected=True));continue
 raise AssertionError('mutation accepted: '+label)
(E/'NHC_TESTS.json').write_text(json.dumps(dict(status='PASS',mutations=checks),indent=1)+'\n');print('PASS',len(checks),'mutations rejected')
