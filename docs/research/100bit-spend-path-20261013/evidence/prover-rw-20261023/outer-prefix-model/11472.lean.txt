import R1Z.ProverRwOuterContextModel
import R1Z.ProverRwOuterInstalled
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwOuterTag
open Aeneas Aeneas.Std Result ProverRwFull

def nativeVariant : transport.Variant → ProverRwRngNativeBody.transport.Variant
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D
def tag (v : transport.Variant) : Result U8 :=
  ProverRwRngNativeBody.transport.Variant.tag (nativeVariant v)
def byte : transport.Variant → U8
  | .S1 => 1#u8
  | .S2 => 2#u8
  | .D => 3#u8

theorem tag_source (v : transport.Variant) : tag v = .ok (byte v) := by cases v <;> rfl

variable [ExternalTypes]
@[reducible] def install (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwOuterContext.install ops with op234 := tag}
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  ProverRwCallerBinding.install (install ops)

theorem tag_installed (ops : ExternalFuns) (v : transport.Variant) :
    @transport.Variant.tag _ (selected ops) v = .ok (byte v) := tag_source v

theorem construct_installed (ops : ExternalFuns) (digest nonce : Array U8 32#usize) :
    @aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1 _
      (selected ops) digest nonce =
        .ok (ProverRwOuterContextModel.context digest nonce) :=
  ProverRwOuterContext.construct_fields digest nonce

theorem encode_installed (ops : ExternalFuns) (c : ProverRwOuterContext.Context) :
    @aspis_core.state_only_hiding.StateOnlyHidingContext.encode _ (selected ops) c =
      .ok (ProverRwOuterEncode.value c) := ProverRwOuterEncode.encode_total c

#print axioms tag_source
#print axioms tag_installed
#print axioms construct_installed
#print axioms encode_installed
end R1Z.ProverRwOuterTag
