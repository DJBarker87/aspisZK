import NIW_AlignFieldReply
import NHX_FactoredPacket
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFactoredReply
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts

theorem source (ap0 ap1 : Powers) (extra : Array K 2#usize)
 (c0 : canonical ap0) (c1 : canonical ap1) (ce : NHI_CellCanon.array extra) :
 FIo_Native.weights.factored_s2_libra_weights ap0 ap1 extra=NHX_FactoredPacket.reference ap0 ap1 extra ∧
 NIW_AlignFieldReply.Produced (FIo_Native.weights.factored_s2_libra_weights ap0 ap1 extra)
  (fun weights=>canonical weights) := by
 obtain ⟨weights,native,model,canon⟩ := NHX_FactoredPacket.source ap0 ap1 extra c0 c1 ce
 refine ⟨native.trans model.symm,?_⟩
 rw [native]
 exact canon

#print axioms source
end AspisR1.NIW_AlignFactoredReply
