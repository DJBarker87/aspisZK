from pathlib import Path
import re,json,hashlib,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];rows=json.loads((E/'NFU_RETARGET.json').read_text());diff=(E/'NFU_RETARGET.diff').read_text()
for n in ['LPl_G_StopRule','LPl_G_Validation','LPl_Validate']:
 p=R/'evidence/leaf-p6-10-20261027'/(n+'.lean');raw=p.read_text();s=re.sub(r'^import (LPl_\S+)',r'import NFU_\1',raw,flags=re.M);lines=s.splitlines(True);last=max(i for i,l in enumerate(lines)if l.startswith('import '));lines.insert(last+1,'\nnamespace NFU_Retarget\n');s=''.join(lines)+'\nend NFU_Retarget\n';(E/('NFU_'+n+'.lean')).write_text(s)
 rows.append(dict(module='NFU_'+n,origin=str(p.relative_to(R)),origin_sha256=hashlib.sha256(raw.encode()).hexdigest(),source_sha256=hashlib.sha256(s.encode()).hexdigest(),transformation='Imports -> NFU_; enclosing namespace NFU_Retarget; all proof terms unchanged'))
 diff+=''.join(difflib.unified_diff(raw.splitlines(True),s.splitlines(True),fromfile='a/'+str(p.relative_to(R)),tofile='b/'+str((E/('NFU_'+n+'.lean')).relative_to(R))))
(E/'NFU_RETARGET.json').write_text(json.dumps(rows,indent=1)+'\n');(E/'NFU_RETARGET.diff').write_text(diff)
p=E/'NFU_CompactLeaves.lean';s=p.read_text().replace('import NFU_LPl_Check','import NFU_LPl_Check\nimport NFU_LPl_Validate')
idx=s.index('#print axioms check_result')
code='''/-- Complete row/error-index Result of the retained validator packet. -/
theorem validate_result (row : U8) (bytes : Slice U8) (out : Option Nat)
    (bound : bytes.val.length ≤ 3712)
    (trace : LPl.Scan.Trace (LPl.Validate.predicate bytes.val) (bytes.val.length / 32) 0 out) :
    NFU_Retarget.r1_wire.validate_record_fields row bytes =
      match out with
      | none => ok (.Ok ())
      | some i => if h : i ≤ UScalar.cMax .Usize then
          ok (.Err (.NonCanonical row (UScalar.ofNat i h))) else fail .panic :=
  LPl.Validate.native_result row bytes out bound trace

#print axioms validate_result
'''
s=s[:idx]+code+s[idx:];p.write_text(s)
(E/'NFU_QUEUE09.json').write_text(json.dumps([dict(attempt=f'NFU_L{i:03}',kind='lean',target='NFU_'+n,exit=0)for i,n in [(47,'LPl_G_StopRule'),(48,'LPl_G_Validation'),(49,'LPl_Validate'),(50,'CompactLeaves')]],indent=1)+'\n')
