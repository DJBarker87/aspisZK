from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent
raw=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-core/src/field.rs'],text=True)
def body(text,marker):
 p=text.index(marker);start=text.index('{',p);depth=1;i=start+1
 while depth:
  if text[i]=='{':depth+=1
  if text[i]=='}':depth-=1
  i+=1
 return text[start+1:i-1]
def clean(s):
 s=re.sub(r'//[^\n]*','',s);s=re.sub(r'\s+','',s);return re.sub(r',([}\]])',r'\1',s)
q=body(raw,'pub fn square(self) -> QM31')
q=q.replace('        #[cfg(feature = "r0-op-count")]\n        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::KSquare);\n','')
transformed=q.replace('self','value').replace('value.c0.square()','op(log,0,value.c0,CM31::ZERO)').replace('value.c1.square()','op(log,1,value.c1,CM31::ZERO)').replace('value.c0.mul(value.c1)','op(log,2,value.c0,value.c1)')
logged=body((E/'NGH_qsquare.rs.txt').read_text(),'fn logged(')
assert clean(transformed)==clean(logged)
ref=(E/'NGH_reference.rs.txt').read_text()
for a,b in [('fn qm31_accumulate_product_channels(','fn NGH_accumulate_ref('),('fn qm31_sum_products_small<','fn NGH_small_ref<')]:
 before=body(raw,a);after=body(ref,b).replace('NGH_accumulate_ref','qm31_accumulate_product_channels');assert clean(before)==clean(after)
x=dict(status='PASS',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_field_sha256=hashlib.sha256(raw.encode()).hexdigest(),QM_square=dict(frozen_body=q,local_record_body=logged,opaque_sites=['CM31.square(value.c0)','CM31.square(value.c1)','CM31.mul(value.c0,value.c1)'],real_calls=['mul_by_r','CM31.add','CM31.double'],normalised_tokens_equal=True,op_count_erased_reason='cfg r0-op-count absent; exact selected core features [r0] in every native graph receipt'),helper_reference_bodies_equal_modulo_names=True,helper_native_contract=False,trust='handwritten helper reference/Lean transcription under (ah); not silently substituted for a missing native helper contract')
(E/'NGH_SOURCE_ASSOCIATION.json').write_text(json.dumps(x,indent=1)+'\n');print('source association PASS')
