#!/usr/bin/env python3
"""Reuse retained actual context declarations with a pinned constant leaf."""
from pathlib import Path
import argparse,hashlib,json
root=Path(__file__).resolve().parents[2]
source=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngNativeBodyEmission.lean'
s=source.read_text();start=s.index('def aspis_core.state_only_hiding.StateOnlyHidingContext.encode\n');end=s.index('\n/--',start);decl=s[start:end]
version='  let i ← aspis_core.state_only_hiding.STATE_ONLY_HIDING_CONTEXT_VERSION\n'
assert decl.count(version)==1
native=root/'crates/aspis-core/src/state_only_hiding.rs'
assert native.read_text().count('pub const STATE_ONLY_HIDING_CONTEXT_VERSION: u8 = 1;')==1
encode=decl.replace('def aspis_core.state_only_hiding.StateOnlyHidingContext.encode','def encode',1).replace(version,'  let i := 1#u8\n')
text='''import R1Z.ProverRwOuterPrefix
import R1Z.ProverRwRngNativeBodyEmission
/-! Two concrete source operations for the public prefix, reused from the
retained actual-body extraction. This is not a native ROM/OS interpretation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwOuterContext
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext
abbrev NativeContext := ProverRwRngNativeBody.aspis_core.state_only_hiding.StateOnlyHidingContext

def toNative (c : Context) : NativeContext :=
  ⟨c.statement_digest,c.mask_nonce,c.mask_layout_fingerprint,c.layout_factor_fingerprint⟩
def fromNative (c : NativeContext) : Context :=
  ⟨c.statement_digest,c.mask_nonce,c.mask_layout_fingerprint,c.layout_factor_fingerprint⟩

theorem context_roundtrip (c : Context) : fromNative (toNative c) = c := by cases c; rfl

def construct (digest nonce : Array U8 32#usize) : Result Context := do
  let c ← ProverRwRngNativeBody.aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1 digest nonce
  .ok (fromNative c)

'''+encode+'''

theorem construct_fields (digest nonce : Array U8 32#usize) :
    construct digest nonce = .ok ⟨digest,nonce,18003970557850322385#u64,7605398817818846427#u64⟩ := by
  simp only [construct,fromNative,
    ProverRwRngNativeBody.aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1,
    ProverRwRngNativeBody.aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1,
    ProverRwRngNativeBody.aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1,
    bind_tc_ok]

/-- All other LocalLeaves fields are unused by this operation. The version
leaf is the literal existing Rust constant, not an environmental hypothesis. -/
theorem encode_source [ProverRwRngNativeBody.TypeLeaves]
    (leaves : ProverRwRngNativeBody.LocalLeaves) (c : Context) :
    encode c = @ProverRwRngNativeBody.aspis_core.state_only_hiding.StateOnlyHidingContext.encode
      _ {leaves with f11 := .ok 1#u8} (toNative c) := by rfl

variable [ExternalTypes]
@[reducible] def install (ops : ExternalFuns) : ExternalFuns :=
  {ops with op115 := construct, op116 := encode}

theorem construct_installed (ops : ExternalFuns) (digest nonce : Array U8 32#usize) :
    @aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1 _ (install ops) digest nonce =
      construct digest nonce := by rfl

theorem encode_installed (ops : ExternalFuns) (c : Context) :
    @aspis_core.state_only_hiding.StateOnlyHidingContext.encode _ (install ops) c = encode c := by rfl

#print axioms context_roundtrip
#print axioms construct_fields
#print axioms encode_source
#print axioms construct_installed
#print axioms encode_installed
end R1Z.ProverRwOuterContext
'''
out=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwOuterContext.lean'
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
if a.check: assert out.read_text()==text
else: out.write_text(text)
print(json.dumps({'retained_source':str(source.relative_to(root)),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'declaration_sha256':hashlib.sha256(decl.encode()).hexdigest(),'native_constant_source':str(native.relative_to(root)),'native_source_sha256':hashlib.sha256(native.read_bytes()).hexdigest(),'constant':'STATE_ONLY_HIDING_CONTEXT_VERSION=1','output_sha256':hashlib.sha256(text.encode()).hexdigest(),'substitutions':['nominal full-caller Context record','f11 literal existing constant1; no other operation change']}))
