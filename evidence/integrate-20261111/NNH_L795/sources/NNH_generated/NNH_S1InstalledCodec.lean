import NNH_HostExec
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_S1InstalledCodec
open Aeneas Aeneas.Std Result NNH_HostCtx NNH_S1HostCodec

theorem validate_slot {W Tx : Type} (c : Ctx W Tx) (st : Statement) :
 (sdk c).op21 st = validate st := rfl

theorem encode_slot {W Tx : Type} (c : Ctx W Tx) (a : Afterstate) :
 (sdk c).op24 a = encode a := rfl

theorem validate_ok {W Tx : Type} (c : Ctx W Tx) (st : Statement)
 (good : NNH_Libraries.C.validateStatement (NNH_S1DecodeOk.carrier st) = true) :
 (sdk c).op21 st = .ok (.Ok ()) := by
 rw [validate_slot]
 exact NNH_S1HostCodec.validate_ok st good

theorem encode_ok {W Tx : Type} (c : Ctx W Tx) (a : Afterstate) (out : Array U8 688#usize)
 (called : NMT_345.encodeCall (afterCarrier a) = .ok (.Ok out)) :
 (sdk c).op24 a = .ok (.Ok out) := by
 rw [encode_slot]
 exact NNH_S1HostCodec.encode_ok a out called
#print axioms validate_slot
#print axioms encode_slot
#print axioms validate_ok
#print axioms encode_ok
end AspisR1.NNH_S1InstalledCodec
end
