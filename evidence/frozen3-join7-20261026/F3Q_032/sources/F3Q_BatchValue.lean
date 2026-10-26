import F3Q_IdealCode
import Port9OR_BatchLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_BatchValue
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem body {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (law : ∀ parts,D.digest hash parts=ok (MultiproofConePhysicalTransport.rawOracle H parts))
    (proof : Slice U8) (root : Array U8 32#usize) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (idx : Port9OR_BatchStep.Indices) (val : Port9OR_BatchStep.Values) (d pos : Usize) :
    (eval H (SdkC_Oracle.program (Port9OR_BatchStep.body Port4B_Install.leaves D proof root tree hash
      lo n slot keys idx val d pos))).2=
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body Port4B_Install.leaves
      D proof root tree hash lo n slot keys idx val d pos := by
  rw [F3Q_IdealCode.value D hash H law,Port9OR_BatchStep.source]
  rfl

#print axioms body
end AspisR1.F3Q_BatchValue
end
