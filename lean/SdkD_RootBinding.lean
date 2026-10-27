import SdkD_ModelRoots
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_RootBinding
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical OraclePortCompactDraft OraclePortBatchDraft

theorem root0 (p : Parsed) (root : Array U8 32#usize)
    (physical : bytesOf root.val = slice p.wire 16 32) :
    root = encodeState (committedRoot p 0) := by
  have decoded : committedRoot p 0 = decodeState root := by
    simp only [committedRoot,ite_true,OraclePortCompactDraft.root0,←physical,
      SdkD_ModelRoots.decode_native,Option.getD_some]
  rw [decoded]
  exact (array_roundtrip root).symm

theorem root1 (stored : Bytes) (p : Parsed) (parsed : parse stored = some p)
    (root : Array U8 32#usize) (physical : bytesOf root.val = slice p.wire 63 32) :
    root = encodeState (committedRoot p 1) := by
  have decoded : committedRoot p 1 = decodeState root := by
    simp only [committedRoot,show ¬(1:Nat)=0 by decide,if_false,ite_true,
      SdkD_SliceAlgebra.root1 stored p parsed,←physical,SdkD_ModelRoots.decode_native,Option.getD_some]
  rw [decoded]
  exact (array_roundtrip root).symm

theorem current (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared)
    (stored : Bytes) (parsed : Parsed) (parser : parse stored = some parsed)
    (wire : parsed.wire = bytesOf proof.val) (r0 r1 : Array U8 32#usize)
    (roots : p.roots = Array.make 2#usize [r0,r1])
    (physical0 : r0.val = proof.val.slice 16 48) (physical1 : r1.val = proof.val.slice 63 95) :
    Port3_BatchStage.root0 (Tx1Q_Carriers.prepared p) = encodeState (committedRoot parsed 0) ∧
    Port3_BatchStage.root1 (Tx1Q_Carriers.prepared p) = encodeState (committedRoot parsed 1) := by
  have b0 : bytesOf r0.val = slice parsed.wire 16 32 := by
    rw [physical0,SdkD_ModelRoots.rawSlice,wire]
  have b1 : bytesOf r1.val = slice parsed.wire 63 32 := by
    rw [physical1,SdkD_ModelRoots.rawSlice,wire]
  have zero : Port3_BatchStage.root0 (Tx1Q_Carriers.prepared p) = r0 := by
    simp only [Port3_BatchStage.root0,Tx1Q_Carriers.prepared,roots,Array.make]
    rfl
  have one : Port3_BatchStage.root1 (Tx1Q_Carriers.prepared p) = r1 := by
    simp only [Port3_BatchStage.root1,Tx1Q_Carriers.prepared,roots,Array.make]
    rfl
  exact ⟨zero.trans (root0 parsed r0 b0),one.trans (root1 stored parsed parser r1 b1)⟩

#print axioms root0
#print axioms root1
#print axioms current
end AspisR1.SdkD_RootBinding
end
