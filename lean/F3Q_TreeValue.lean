import F3Q_IdealCode
import Port9OR_BatchTree
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_TreeValue
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem value {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (law : ∀ parts,D.digest hash parts=ok (MultiproofConePhysicalTransport.rawOracle H parts))
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
    (batch kind : Usize) (idx : Port9OR_BatchStep.Indices) (val : Port9OR_BatchStep.Values) :
    (eval H (SdkC_Oracle.program (Port9OR_BatchTree.code Port4B_Install.leaves D hash proof queries root batch kind idx val))).2=
    Port3_NativeBatchBody.verifier.candidate.batch_tree Port4B_Install.leaves D proof queries root batch kind idx val hash := by
  rw [F3Q_IdealCode.value D hash H law,Port9OR_BatchTree.source]
  rfl

#print axioms value
end AspisR1.F3Q_TreeValue
end
