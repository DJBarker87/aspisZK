"""Rule y-prime source identities with rejected wrong-place/effect mutations."""
from pathlib import Path
import subprocess,json,re,hashlib
E=Path(__file__).resolve().parent
entries=[('178','crates/aspis-statement/src/pool_v1/incremental_merkle.rs','fn as_tree(&self)','{ &self.inner }','receiver.inner'),('176','crates/aspis-statement/src/pool_v1/incremental_merkle.rs','fn deref(&self)','{ self.as_tree() }','receiver.inner via CLOSED178'),('291','programs/aspis-pool/src/nullifier.rs','fn seed(&self)','{ &self.seed }','receiver.seed'),('343','programs/aspis-pool/src/pair_forest_dispatch.rs','fn value(&self)','{ &self.value }','receiver.value.deref (std Box)'),('355','programs/aspis-pool/src/pair_state.rs','fn deref(&self)','{ &self.state }','receiver.state.deref (std Box)')]
def tokens(s):return re.findall(r'\w+|[^\s]',s)
def body(s,needle):
 a=s.index(needle);a=s.index('{',a);level=0
 for b in range(a,len(s)):
  level+=(s[b]=='{')-(s[b]=='}')
  if level==0:return s[a:b+1]
 raise AssertionError('unclosed function')
rows=[]
for id,path,needle,expected,place in entries:
 rev='b936275465600469312d1f058cdc91ea2a11f3dc' if path.startswith('programs/') else '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';s=subprocess.check_output(['git','show',rev+':'+path],text=True);actual=body(s,needle);check=lambda x:tokens(x)==tokens(expected);assert check(actual)
 mutants=[actual.replace('self.','other.'),'{ panic!("wrong place") }','{ &WRONG_PLACE }','{ log_effect(); '+actual[1:-1]+' }']
 assert all(not check(m) for m in mutants)
 rows.append(dict(id='POOL:'+id,source=path,revision=rev,body=actual,body_sha256=hashlib.sha256(actual.encode()).hexdigest(),borrowed_place=place,mutability='shared',lifetime='loan of actual receiver',modifies=[],own_argument_domain='any valid live immutable Rust receiver; no additional semantic predicate',source_identity=True,mutations_rejected=len(mutants),mutations=mutants,dependency='POOL:178 must be CLOSED before176 credit' if id=='176' else None))
(E/'PCB_GETTER_IDENTITIES.json').write_text(json.dumps(dict(rule='y-prime source identity + extracted-body Lean identity + wrong-place caller control; no stub_verified borrowed return',rows=rows,shared_generic_reference='PCB_getter_reference.rs',generic_parameter_scope='unused preparation/program carriers and boxed pointee are polymorphic; no ABI/layout equality claimed',M31_model='actual E003 extraction erases M31 newtype to Std.U32; no field arithmetic performed'),indent=1)+'\n')
print('PCB getter identity PASS: five exact bodies;20 wrong-place/effect mutations rejected')
