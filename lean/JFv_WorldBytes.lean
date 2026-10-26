import JFv_WorldAdmission
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_WorldBytes
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open JFv_World CPG_Projection CPP_BankState Hist_RuntimeEntry
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.publicInput JFx_NativeBytes.checkpoint

theorem inputs (proofAccount : Slice U8) :
    (e1 proofAccount).buffers ((e1 proofAccount).handles 0).1=proofAccount ∧
    (e2 proofAccount).buffers ((e2 proofAccount).handles 0).1=proofAccount ∧
    (e1 proofAccount).buffers ((e1 proofAccount).handles 1).1=JFx_NativeBytes.publicInput ∧
    (e2 proofAccount).buffers ((e2 proofAccount).handles 6).1=JFx_NativeBytes.checkpoint := by
  simp [e1,e2,entry,observations,initial,buffer,final,cached,load,
    CPP_BankState.layout,CPH_FixtureData.layout1,CPH_FixtureData.layout2,
    CPH_FixtureData.readerCell,CPR_SourceBank.afterCopy,commit,Hist_Store.put,saved,
    alloc.vec.Vec.deref]

theorem checkpoint_before (proofAccount : Slice U8) :
    ((e1 proofAccount).buffers ((e1 proofAccount).handles 2).1).length=1768 := by
  change (CPH_FixtureData.zeros 1768 (by decide)).length=1768
  exact List.length_replicate

#print axioms inputs
#print axioms checkpoint_before
end AspisR1.JFv_WorldBytes
end
