from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def method(file,name):
 s=subprocess.check_output(['git','show',REV+':crates/aspis-core/src/'+file],text=True)
 a=s.index('pub fn '+name+'(');b=s.index('{',a);end=b+1;depth=1
 while depth:depth+=(s[end]=='{')-(s[end]=='}');end+=1
 return s[a:end]
rows=[];out=[]
for file,name in [('circle.rs','secure_circle_point_from_parameter'),('circle.rs','secure_ood_circle_point_from_parameter'),('transcript.rs','circle_fallback_point')]:
 raw=method(file,name);s=raw
 if name=='secure_circle_point_from_parameter':
  s=s.replace('parameter: QM31,','parameter: QM31, l: &mut Log,')
  s=s.replace('parameter.square()','square(l,parameter)')
  s=s.replace('QM31::ONE\n        .add(square)\n        .try_inv()','inverse(l,add(l,QM31::ONE,square))')
  # Split nested mutable borrows preserving call order.
  s=s.replace('let inverse_denominator = inverse(l,add(l,QM31::ONE,square))','let denominator = add(l,QM31::ONE,square);\n    let inverse_denominator = inverse(l,denominator)')
  s=s.replace('QM31::ONE.sub(square).mul(inverse_denominator)','{ let n=sub(l,QM31::ONE,square); product(l,n,inverse_denominator) }')
  s=s.replace('parameter.add(parameter).mul(inverse_denominator)','{ let n=add(l,parameter,parameter); product(l,n,inverse_denominator) }')
 elif name=='secure_ood_circle_point_from_parameter':
  s=s.replace('parameter: QM31,','parameter: QM31, l: &mut Child,').replace('secure_circle_point_from_parameter(parameter)?','child(parameter,l)?')
 else:
  s=s.replace('sample: usize)','sample: usize,l: &mut Child)').replace('secure_ood_circle_point_from_parameter(parameter)','child(parameter,l)')
 out.append(s);rows.append(dict(function=name,frozen_body=raw,cut_body=s,frozen_sha256=hashlib.sha256(raw.encode()).hexdigest(),cut_sha256=hashlib.sha256(s.encode()).hexdigest()))
(E/'NKM_NATIVE_CORRESPONDENCE.json').write_text(json.dumps(rows,indent=2)+'\n')
(E/'NKM_native_generated.rs.txt').write_text((E/'NKM_native.rs.txt').read_text().replace('NKM_METHODS','\n'.join(out)))
