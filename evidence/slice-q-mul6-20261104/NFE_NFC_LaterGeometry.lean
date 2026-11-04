import NFE_NFC_LaterSource
import NFC_CheckedArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFE_NFC_LaterGeometry
open Aeneas Aeneas.Std Result NEV_DotCarrier NFE_NFC_TailSources

theorem accepted (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (slot base position : Usize) (inside : slot.val<4) (active : position.val<2)
    (baseEq : slot*32#usize=ok base) (value : NE) (scalar : NQ)
    (run : later q g base position=ok (value,scalar)) :
    ∃ start stop index,
      NFA_TailQM.read q start stop=ok scalar ∧ Array.index_usize g index=ok value ∧
      start.val=480+slot.val*32+position.val*16 ∧ stop.val=start.val+16 ∧
      index.val=position.val+26 ∧ 480≤start.val ∧ stop.val≤608 ∧ index.val<29 := by
  obtain ⟨origin,offset,start,index,stop,originEq,offsetEq,startEq,indexEq,read,stopEq,decode⟩:=
    NFE_NFC_LaterSource.cut q g base position value scalar run
  have b:=NFC_CheckedArithmetic.mul slot 32#usize base (by scalar_tac) baseEq
  have o:=NFC_CheckedArithmetic.add 480#usize base origin (by scalar_tac) originEq
  have f:=NFC_CheckedArithmetic.mul position 16#usize offset (by scalar_tac) offsetEq
  have a:=NFC_CheckedArithmetic.add origin offset start (by scalar_tac) startEq
  have i:=NFC_CheckedArithmetic.add position 26#usize index (by scalar_tac) indexEq
  have z:=NFC_CheckedArithmetic.add start 16#usize stop (by scalar_tac) stopEq
  refine ⟨start,stop,index,decode,read,?_,?_,?_,?_,?_,?_⟩ <;> scalar_tac
#print axioms accepted
end AspisR1.NFE_NFC_LaterGeometry
end
