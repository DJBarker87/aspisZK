#!/usr/bin/env python3
"""Audit generated discriminator name-only transports for joint Lean imports."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
from qualify_discriminants import qualify
start=time.monotonic();tool=Path(__file__).resolve().parent;area=tool.parents[1];ev=area/'evidence/cu-equivalence-20261019'
records=[]
raw=(tool/'cu-gamma-generated/Types.lean').read_bytes();p=area/'lean/AspisR1CuGamma/Types.lean'
assert p.read_bytes()==qualify(raw,'AspisR1CuGamma')
for script in ['emit-gamma-callers.py','emit-s2-groups.py','emit-cu-query.py','emit-profiling-source.py']:
 subprocess.run([sys.executable,str(tool/script),'--check'],check=True,stdout=subprocess.PIPE)
for ns in ['AspisR1CuGamma','AspisR1CuGammaCall','AspisR1S2Groups','AspisR1CuQuery','AspisR1Profiling']:
 p=area/'lean'/ns/'Types.lean';text=p.read_text()
 registrations=re.findall(r'instance _root_\.([A-Za-z0-9_.]+)\s*:\s*Aeneas.Std.Discriminant\s+([A-Za-z0-9_.]+)\s+Isize',text)
 assert registrations,(ns,'no qualified registrations')
 assert '@[discriminant isize]' not in text,(ns,'unqualified macro remains')
 records.append({'module':ns+'.Types','source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'qualified_instances':[name for name,enum in registrations],'constructors_order_and_ordinal_equations':'unchanged, inverse checked against exact raw generated source; see normalizers'})
u=resource.getrusage(resource.RUSAGE_SELF)
report={'status':'QUALIFIED_REGISTRATION_ONLY_TRANSPORT_CHECKED','reason':'Actual joint import rejected colliding generated global instance names; first failed focused receipt retained-closure-nine-a.','statement_or_rust_computation_changes':False,'records':records,'normalizers':['qualify_discriminants.py','emit-gamma-callers.py','emit-s2-groups.py','emit-cu-query.py','emit-profiling-source.py'],'refresh_manifest':'qualified-registration-selected.json','audit':{'command':[sys.executable,*sys.argv],'revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'features':[],'exit':0,'wall_seconds':time.monotonic()-start,'peak_rss_bytes':u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,'process_swaps':u.ru_nswap,'print_axioms':'N/A Python transport audit; refreshed focused Lean targets supply exact axioms'}}
(ev/'QUALIFIED-REGISTRATIONS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'registration_name_only':True,'modules':len(records)}))
