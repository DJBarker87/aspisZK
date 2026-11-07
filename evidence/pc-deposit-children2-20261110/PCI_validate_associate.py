from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
row=next(r for r in json.loads((E/'PCI_SOURCE_MAP.json').read_text()) if r['id']=='POOL:223')
frozen=row['frozen_function'];body=frozen[frozen.index('{'):].replace('self','w')
scan="""w
            .second_commitment
            .iter()
            .any(|limb| one_minus_occupied.mul(*limb) != M31::ZERO)"""
assert scan in body
expected=body.replace(scan,'scan_nonzero')
transforms=[('w.second_occupied.mul(w.second_occupied.sub(M31::ONE))','mul_window(w.second_occupied, w.second_occupied.sub(M31::ONE), log)'),('w.second_sentinel().mul(w.second_occupancy_inverse)','mul_window(w.second_sentinel(), w.second_occupancy_inverse, log)'),('one_minus_occupied.mul(w.second_occupancy_inverse)','mul_window(one_minus_occupied, w.second_occupancy_inverse, log)')]
for a,b in transforms:assert a in expected;expected=expected.replace(a,b)
fission=(E/'PCI_ValidateFission.rs').read_text();fb=fission[fission.index('{'):].strip()
norm=lambda x:re.sub(r'\s+','',x)
assert norm(fb)==norm(expected)
assert norm(fb.replace('OccupiedSentinelZero','SentinelInverseMismatch'))!=norm(expected)
assert norm(fb.replace('w.second_occupied.sub(M31::ONE)','w.second_occupied'))!=norm(expected)
# Match each smaller source window around the CLOSED field call.
windows=(E/'PCI_ValidateWindows.rs').read_text()
expected_gate=expected[:expected.index('    let one_minus_occupied')]+'    Ok(())\n}\n'
assert norm(expected_gate) in norm(windows)
for index,marker in enumerate(['if mul_window(w.second_occupied, w.second_occupied.sub(M31::ONE), log)','if mul_window(w.second_sentinel(), w.second_occupancy_inverse, log)','if mul_window(one_minus_occupied, w.second_occupancy_inverse, log)']):
 a=expected.index(marker);start=expected.index('{',a);depth=0
 for stop in range(start,len(expected)):
  depth+=int(expected[stop]=='{')-int(expected[stop]=='}')
  if depth==0:break
 block=expected[a:stop+1]
 full=transforms[index][1]
 block=block.replace(full,'product').replace('w.second_occupied','occupied')
 assert norm(block) in norm(windows)
assert norm(expected[expected.index('    if scan_nonzero'):]) in norm(windows)
s=(E/'PCI_ValidateNative.rs').read_text()
assert 'fn scan_arguments(one_minus_occupied:M31,limb:M31)->[M31;2]{[one_minus_occupied,limb]}' in s
assert 'fn scan_after_product(product:M31)->bool{product!=M31::ZERO}' in s
assert '#[kani::stub(M31::mul,product_spec)]' not in s
x=json.loads((E/'PCI_ASSOCIATIONS.json').read_text());x=[r for r in x if r['row']!='POOL:223']
x.append(dict(row='POOL:223',frozen_body_sha256=row['frozen_body_sha256'],fission_sha256=hashlib.sha256(fission.encode()).hexdigest(),transforms=transforms,loop_cut=scan,loop_predicate='one_minus_occupied.mul(*limb) != M31::ZERO',exact_after_named_erasure=True,windows_sha256=hashlib.sha256(windows.encode()).hexdigest(),field_calls="CLOSED PCI_Mul.value composed in Lean at SAME operands; no accepted native product stub",mutations_rejected=['error constructor','product operand'],classification='ReviewedTranscription of prefix and one iteration; Lean fold and CLOSED callee substitution still required'))
(E/'PCI_ASSOCIATIONS.json').write_text(json.dumps(x,indent=1)+'\n')
print('PCI223 exact prefix and predicate association; two mutations rejected')
