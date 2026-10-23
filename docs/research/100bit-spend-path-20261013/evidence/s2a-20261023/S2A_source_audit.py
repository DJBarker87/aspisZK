#!/usr/bin/env python3
"""No prover replay: exact caller erasure, source pins and model scope checks."""
from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent;R=E.parents[4]
source=(R/'programs/r1-cost-probe/src/r1_pool_adapter.rs').read_text()
def function(s,name):
 a=s.index('fn '+name);b=s.index('{',a);depth=1;i=b+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
versions=[]
for v in [1,2,3]:
 p=E/f'S2A-native-v{v}';s=(p/'src/lib.rs').read_text();cut=json.loads((p/'source-cut.json').read_text());assert hashlib.sha256(s.encode()).hexdigest()==cut['source_sha256']
 native=function(s,'stage1(');fission=cut['scan_fission'];observed_fission=fission['replacement'].replace('crate::proofs::','crate::S2A_native::');assert native.count(observed_fission)==1;erased=native.replace(observed_fission,fission['original']);assert erased==function(source,'stage1(')
 for name in ['readonly_buffer_meta_ok(','require_readonly_buffer(','require_verifier_checkpoint(','require_distinct_accounts<','decode_public_statement_box(']:assert function(s,name)==function(source,name),name
 assert not re.search(r'#\[kani::stub(?:_verified)?\(AccountInfo::',s)
 assert 'if kani::any::<bool>() {' in s and s.count('RETURNED.value[')>=6
 assert 'PLAN.value=Some(Plan{statement:statement(),candidate:kani::any()' in s
 assert not re.search(r'copy_nonoverlapping\(plan\(\)\.candidate|b0\[696\]=2|buffers\[0\]\[696\]=2',s)
 versions.append({'version':v,'source_sha256':cut['source_sha256'],'erased_stage1_sha256':hashlib.sha256(erased.encode()).hexdigest(),'scope':'first-entry open typed children; no native child/source/runtime interpretation certified'})
# The adopted primitive body/contract is reused unchanged after consumer-only edits.
a=(E/'S2A-spec/source-v1.rs.txt').read_text();b=(E/'S2A-spec/S2A_Primitives.rs').read_text();marker='// Capacity extension only:';assert a.split(marker)[0]==b.split(marker)[0]
old=(R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021/S2SdkReadyRawInputsV1.lean').read_text();new=(R/'docs/research/100bit-spend-path-20261013/lean/S2A_ReadyInputs.lean').read_text()
old_sig=old[old.index('theorem construct ('):old.index(' := by\n  have proofAllowed')];new_sig=new[new.index('theorem construct_without_validator ('):new.index(' := by\n  obtain')]
expected=old_sig.replace('theorem construct (ops : Ops)','theorem construct_without_validator (ops : SdkReference.Ops)').replace('    (validated : (Installation.install ops verifierOps).op5 statement=ok (.Ok ()))\n','');assert new_sig==expected
out={'versions':versions,'constructor_change':'only independent validated hypothesis removed; every other binder/conclusion byte-identical modulo theorem and qualified Ops names','production_source_changed':False,'new_native_execution_certificate':False}
(E/'source-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
