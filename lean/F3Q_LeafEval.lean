import F3Q_CodeEval
import Port4B_LeafCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_LeafEval
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
open MultiproofConeSlices

theorem leaf (H : Bytes → State) (kind : Usize) (o : Slice U8) (len : o.val.length=832) :
    eval H (SdkC_Oracle.program (Port4B_LeafCode.code kind o))=
      ([(flatten (Port4B_LeafCode.input kind o),H (flatten (Port4B_LeafCode.input kind o)))],
       ok (encodeState (H (flatten (Port4B_LeafCode.input kind o))))) := by
  have range (s e : Usize) (order : s.val≤e.val) (fit : e.val≤832) :
      Port4B_LeafCode.readRange o s e=ok (sub o s e) :=
    range_total o s e order (by omega)
  unfold Port4B_LeafCode.code Port4B_LeafCode.input
  split
  · simp only [Port4B_LeafCode.codeFor,SdkC_Oracle.program,eval,
      range 608#usize 640#usize (by decide) (by decide),range 0#usize 480#usize (by decide) (by decide)]
  · split
    · simp only [Port4B_LeafCode.codeFor,SdkC_Oracle.program,eval,
        range 640#usize 672#usize (by decide) (by decide),range 480#usize 608#usize (by decide) (by decide)]
    · simp only [Port4B_LeafCode.codeFor,SdkC_Oracle.program,eval,
        range 800#usize 832#usize (by decide) (by decide),range 672#usize 800#usize (by decide) (by decide)]

#print axioms leaf
end AspisR1.F3Q_LeafEval
end
