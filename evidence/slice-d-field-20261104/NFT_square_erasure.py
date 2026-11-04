from pathlib import Path
import json,subprocess,hashlib,re
E=Path(__file__).resolve().parent;R=E.parents[1]
source=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-core/src/field.rs'],cwd=R,text=True)
harness=json.loads((E/'NFT_NATIVE_INPUTS.json').read_text())['crates/aspis-core/src/NFT_square.rs']
def body(s,marker):
 start=s.index(marker);a=s.index('{',start);depth=1;b=a+1
 while depth:
  depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a+1:b-1]
a=body(source,'pub fn square(self) -> CM31');b=body(harness,'fn square_logged(')
erased=b.replace('product(log,u64::from(value.a.0)+u64::from(value.b.0),u64::from(value.a.0)+u64::from(P)-u64::from(value.b.0))','(u64::from(value.a.0)+u64::from(value.b.0))*(u64::from(value.a.0)+u64::from(P)-u64::from(value.b.0))').replace('multiply(log,value.a,value.b)','value.a.mul(value.b)').replace('value.','self.')
# Rust permits a trailing comma in a single-argument call. Ignore only that trivia.
normalize=lambda s:re.sub(r',\)',')',re.sub(r'\s+','',re.sub(r'//[^\n]*','',s)))
assert normalize(a)==normalize(erased),(a,erased)
assert'kani::any'in body(harness,'fn product(')and'kani::any'in body(harness,'fn multiply(')
assert not re.search(r'\bstatic\s+(?:mut\s+)?\w',harness)
out=dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_function='crates/aspis-core/src/field.rs::CM31::square',frozen_body_sha256=hashlib.sha256(a.encode()).hexdigest(),instrumented_body_sha256=hashlib.sha256(b.encode()).hexdigest(),erasure_equal=True,only_abstractions=['one primitive U64 multiplication replaced by product(log,left,right)','one M31::mul replaced by multiply(log,a,b)'],executed_real_callees=['M31::reduce_u64','M31::double'],order=['wide product','reduce','M31 product','double'],paired_lean=['NFT_Square.wide_product','NFT_Square.generated_scalar_product','NFT_Square.source'],native=['NFT_K020','NFT_K021'],claim='hybrid local-record opaque-site certificate; P6/D188 option A reclassification, never a direct native product-value proof')
(E/'NFT_SQUARE_ERASURE.json').write_text(json.dumps(out,indent=1)+'\n');print('PASS exact two-site erasure')
