import NNH_S1InstalledCodec
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_S1CodecStatus
open Aeneas Aeneas.Std Result NNH_S1HostCodec

theorem validate_exact (st : Statement) :
 validate st = .ok (.Ok ()) ↔ NMT_345.validateCall (NNH_S1DecodeOk.carrier st) = .ok (.Ok ()) := by
 constructor
 · intro returned
   cases h : NMT_345.validateCall (NNH_S1DecodeOk.carrier st) with
   | fail e => simp only [validate,h] at returned; cases returned
   | div => simp only [validate,h] at returned; cases returned
   | ok reply => cases reply with
    | Err e => simp only [validate,h] at returned; cases returned
    | Ok u => cases u; rfl
 · intro called
   unfold validate
   rw [called]

theorem encode_exact (a : Afterstate) (out : Array U8 688#usize) :
 encode a = .ok (.Ok out) ↔ NMT_345.encodeCall (afterCarrier a) = .ok (.Ok out) := by
 constructor
 · intro returned
   cases h : NMT_345.encodeCall (afterCarrier a) with
   | fail e => simp only [encode,h] at returned; cases returned
   | div => simp only [encode,h] at returned; cases returned
   | ok reply => cases reply with
    | Err e => simp only [encode,h] at returned; cases returned
    | Ok value =>
     simpa only [encode,h] using returned
 · intro called
   exact NNH_S1HostCodec.encode_ok a out called
#print axioms validate_exact
#print axioms encode_exact
#check AspisS6CurrentFirstInstallation.current
#check _root_.AdapterRw.Ops.op10
end AspisR1.NNH_S1CodecStatus
end
