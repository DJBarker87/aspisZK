import NMT_R2_PrefixPacket
import NMT_R2_MiddlePacket
import NMT_R2_BoundsPacket
import NMT_R2_TailPacket
import NMT_345SelectedFold
set_option autoImplicit false
noncomputable section
namespace NMT_R2_SelectedPacket
open Aeneas Aeneas.Std NMT_345

def selected {W : Type} (c : Calls) (s : Selected W) : Result (core.result.Result (NMT_R2_TailPacket.Point W) PE) :=
 NMT_R2_ResultTry.bind (NMT_R2_PrefixPacket.packPrefix c s) fun decoded =>
 NMT_R2_ResultTry.bind (NMT_R2_MiddlePacket.middle c decoded) fun proof =>
 NMT_R2_ResultTry.bind (NMT_R2_BoundsPacket.bounds c proof) (NMT_R2_TailPacket.tail c)

theorem source {W : Type} (c : Calls) (s : Selected W) :
 NMT_R2_ResultTry.bind (selected c s) (NMT_R2_TailPacket.finish c) = selectedFold c s := by
 simp only [selected,NMT_R2_ResultTry.assoc,NMT_R2_TailPacket.source,NMT_R2_BoundsPacket.source,
  NMT_R2_MiddlePacket.source,NMT_R2_PrefixPacket.source]
 rfl
#print axioms source
end NMT_R2_SelectedPacket
end
