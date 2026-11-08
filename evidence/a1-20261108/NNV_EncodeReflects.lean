import NNV_AfterstatePort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_EncodeReflects
open Aeneas Aeneas.Std Result NNH_Libraries

theorem source (a : NNH_S1HostCodec.Afterstate) (out : Array U8 688#usize)
 (called : NNH_S1HostCodec.encode a = .ok (.Ok out)) :
 NMT_345.encodeCall (NNH_S1HostCodec.afterCarrier a) = .ok (.Ok out) := by
 unfold NNH_S1HostCodec.encode at called
 cases run : NMT_345.encodeCall (NNH_S1HostCodec.afterCarrier a) with
 | fail e => rw [run] at called; cases called
 | div => rw [run] at called; cases called
 | ok reply =>
  cases reply with
  | Err e => rw [run] at called; cases called
  | Ok bytes =>
   rw [run] at called
   exact run.trans called
#print axioms source
end AspisR1.NNV_EncodeReflects
end
