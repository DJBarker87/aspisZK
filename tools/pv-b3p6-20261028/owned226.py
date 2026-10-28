"""Token-exact native serializer copy for structural binding and finite replay."""
from pathlib import Path
import re,sys,subprocess,hashlib,json
R=Path(__file__).resolve().parents[2];T=R/'tools/pv-b3p6-20261028';D=R/'evidence/pv-b3p6-20261028'
p='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';s=(R/p).read_text()
assert s==subprocess.check_output(['git','show','5fa2cc6781:'+p],cwd=R).decode()
def extract(anchor):
 start=s.index(anchor);a=s.index('{',start);i=a+1;n=1
 while n:
  n+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[start:i]
anchors=['enum CompiledVariant','struct SemanticPublic','fn private_public','fn withdrawal_public',"pub enum Public<'a>"]
methods=['fn semantic(self)','pub fn public_bytes(self)']
code='''//! Token-exact proof-only copy of the native serializer and projection.
use aspis_core::{field::M31,state_only_prefix::r0::Error};
use aspis_statement::{poseidon2::Digest,pool_v1::{
 payment_relation::{PoolV1PrivateTransferPublicV1,PoolV1WithdrawalPublicV1},
 pair_tree_profile::PoolV1PairLatePublicStatementV1}};
'''
for anchor in anchors:
 if anchor=='enum CompiledVariant':code+='#[derive(Clone, Copy, Debug, PartialEq, Eq)]\n'
 elif anchor.startswith(('struct','pub enum')):code+='#[derive(Clone, Copy)]\n'
 code+=extract(anchor)+'\n'
code+="impl<'a> Public<'a> {\n"+'\n'.join(extract(a) for a in methods)+'\n}\n'
out=T/'owned226.rs'
if '--check' in sys.argv:assert out.read_text()==code
else:out.write_text(code)
(D/'owned226-binding.json').write_text(json.dumps(dict(evidence_class='structural (K-1 substitute) candidate',native_source=p,native_sha256=hashlib.sha256(s.encode()).hexdigest(),owned_sha256=hashlib.sha256(code.encode()).hexdigest(),same_bodies=anchors+methods,differences='Imports/namespace only; derives, all fields, calls, constants, checks and error paths are identical.',owned_to_extracted_reference='OPEN until complete region/layout/chunk/Vec value composition',native_link_credit=False,row_closed=False),indent=2)+'\n')
