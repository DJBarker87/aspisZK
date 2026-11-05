import NIL_StatePort
import NHV_PendingPacket
import NID_KmxComposition
set_option autoImplicit false
noncomputable section
namespace NIL_QueryPending
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 NIL_Carriers

def flat (raw : alloc.vec.Vec (Array U64 4#usize)) (k : Nat) : U64 :=
 ((raw.val[k/4]?).map (fun row=>NID_RawWindowFrame.limb row ⟨k%4,Nat.mod_lt _ (by decide)⟩)).getD 0#u64

theorem source (reserved : Bool) (a : NIL_StatePort.F.A) (width : a.weights.val.length=64) :
 Port3_NativePendingInstall.source reserved (NIL_StatePort.accumulator a).weights.deref=
 if reserved then ok (.Ok (NFW_QueryResume.pending (NIL_StatePort.accumulator a)))
 else ok (.Err .Allocation) := by
 apply NHV_PendingPacket.source
 simpa only [NIL_StatePort.accumulator,vec,List.length_map] using width

theorem width (a : NIL_StatePort.F.A) (size : a.weights.val.length=64) :
 (NFW_QueryResume.pending (NIL_StatePort.accumulator a)).raw.val.length=64 := by
 simpa only [NFW_QueryResume.pending,S7Kani3CallerTrace.initialRaw,NFW_QueryResume.rowWeights,
  NIL_StatePort.accumulator,vec,List.length_map] using size

#print axioms width

theorem copied (a : NIL_StatePort.F.A) (before : Nat → U64) (row : Nat) (limb : Fin 4)
 (inside : row<64) :
 NID_KmxComposition.rows (flat (NFW_QueryResume.pending (NIL_StatePort.accumulator a)).raw)
 before 64 (4*row+limb.val)=
 flat (NFW_QueryResume.pending (NIL_StatePort.accumulator a)).raw (4*row+limb.val) :=
 NID_KmxComposition.selected _ _ row limb.val inside limb.isLt

theorem frame (a : NIL_StatePort.F.A) (before : Nat → U64) (k : Nat) (outside : 256≤k) :
 NID_KmxComposition.rows (flat (NFW_QueryResume.pending (NIL_StatePort.accumulator a)).raw)
 before 64 k=before k := by
 rw [NID_KmxComposition.rows_spec,if_neg]
 omega

theorem kmx (a : NIL_StatePort.F.A) (before : Nat → U64) (k : Nat) :
 NID_KmxComposition.rows (flat (NFW_QueryResume.pending (NIL_StatePort.accumulator a)).raw)
 before 64 k=KMX_CopyMeaning.loop (flat (NFW_QueryResume.pending (NIL_StatePort.accumulator a)).raw)
 before 0 256 k := NID_KmxComposition.all64 _ _ k

#print axioms source
#print axioms copied
#print axioms frame
#print axioms kmx
end NIL_QueryPending
