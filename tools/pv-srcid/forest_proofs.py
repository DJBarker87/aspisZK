#!/usr/bin/env python3
"""Port existing symbolic bank proofs to the actual forest extraction namespace.
Does not edit existing modules or source implementations.
The inverse invariant is specialized to the forest extraction's fixed prime.
"""
from pathlib import Path
import re,json,hashlib,sys
check = "--check" in sys.argv
root=Path(__file__).resolve().parents[2]
base=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
order=[];seen=set()
def visit(n):
 if n in seen:return
 seen.add(n);p=base/(n+'.lean')
 if not p.exists():return
 for x in re.findall(r'^import R1Z\.(Builder\w+)',p.read_text(),re.M):visit(x)
 order.append(n)
visit('BuilderPartsComplete')
changed={'BuilderBankExtracted','BuilderColumnsExtracted'}
for n in order:
 s=(base/(n+'.lean')).read_text()
 if 'AspisBuilderGlueSource' in s or 'AspisBuilderColumnsSource' in s or any(x in changed for x in re.findall(r'^import R1Z\.(Builder\w+)',s,re.M)):
  changed.add(n)
mapping={n:'PV_Src_Forest_'+n.removeprefix('Builder') for n in changed if not n.endswith('Extracted')}
manifest=[]
for n in order:
 if n not in mapping:continue
 src=base/(n+'.lean');s=src.read_text()
 s=s.replace('R1Z.BuilderBankExtracted','R1Z.BuilderForestAdmissionPort').replace('R1Z.BuilderColumnsExtracted','R1Z.BuilderForestAdmissionPort')
 s=s.replace('AspisBuilderGlueSource','BuilderForestAdmissionPort').replace('AspisBuilderColumnsSource','BuilderForestAdmissionPort')
 s=s.replace('BuilderForestAdmissionPort.core.','BuilderForestStdPort.core.')
 for a,b in sorted(mapping.items(),key=lambda x:-len(x[0])):s=re.sub(r'\b'+a+r'\b',b,s)
 if n=='BuilderBankRange':
  s=s.replace('import Aeneas.Std.RangeIter','import R1Z.BuilderBankRange')
 if n=='BuilderInverse':
  a=s.index('theorem loop ');b=s.index('theorem field_power_value',a)
  block=s[a:b].replace(' (m : U32) (hm : 1 < m.val)','')
  block=block.replace('m.val','2147483647')
  block=re.sub(r'\bm\b','2147483647#u32',block)
  block=block.replace('inv_r_loop 2147483647#u32 ','inv_r_loop ')
  block=block.replace('multiply_mod 2147483647#u32 hm','multiply_mod 2147483647#u32 (by decide)')
  block=block.replace('multiply_mod 2147483647#u32 (by decide)','multiply_prime')
  block=block.replace('[lift,bind_tc_ok]','[BuilderForestAdmissionPort.aspis_core.field.P,lift,bind_tc_ok]')
  prime="""theorem multiply_prime (a b : U64)
    (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    ∃ c, (U64.wrapping_mul a b % UScalar.cast .U64 2147483647#u32 : Result U64) = ok c ∧
      c.val < 2147483647 ∧ (c.val : ZMod 2147483647) =
        (a.val : ZMod 2147483647) * (b.val : ZMod 2147483647) :=
  multiply_mod 2147483647#u32 (by decide) a b ha hb

"""
  s=s[:a]+prime+block+s[b:]
  s=s.replace('#print axioms loop','#print axioms multiply_prime\n#print axioms loop')
 if n=='BuilderInverseResult':
  s=s.replace('PV_Src_Forest_Inverse.loop 2147483647#u32 (by decide)','PV_Src_Forest_Inverse.loop')
  s=s.replace('inv_r_loop 2147483647#u32 ','inv_r_loop ')
 dest=base/(mapping[n]+'.lean')
 s='/- Namespace port of '+n+': same symbolic proof, actual forest extraction. -/\n'+s
 if check:
  if not dest.exists() or dest.read_text()!=s:raise SystemExit('stale generated source: '+str(dest))
 else:dest.write_text(s)
 manifest.append(dict(origin=str(src.relative_to(root)),origin_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),module=mapping[n],adaptation=('fixed-prime inverse specialization' if n in ['BuilderInverse','BuilderInverseResult'] else 'import/module/namespace identifiers only'),source_sha256=hashlib.sha256(s.encode()).hexdigest()))
manifest_path=root/'evidence/pv-srcid-20261026/forest-proof-provenance.json'
encoded=json.dumps(manifest,indent=2)+'\n'
if check:
 if not manifest_path.exists() or manifest_path.read_text()!=encoded:raise SystemExit('stale forest proof manifest')
else:manifest_path.write_text(encoded)
print('\n'.join(x['module'] for x in manifest))
