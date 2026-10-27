import F3T_Causal
import F3T_Canon
import OraclePortPureOutputC7
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Accounting
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_Charged F3T_Canon

theorem first_reads (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State,(eval H P).1.length≤Q) (H : Bytes → State) :
    firstReads emptyTable (eval H (projected D (canon P))).1≤Q+1161 := by
  rw [projected_eval]
  exact F3T_Bounds.distinct_bound D (build D) (canon P) Q (bound P Q hq) H

theorem log_length (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State,(eval H P).1.length≤Q) (H : Bytes → State) :
    (eval H (projected D (canon P))).1.length≤Q+2322 := by
  rw [projected_eval]
  exact F3T_Bounds.log_length D (build D) (canon P) Q (bound P Q hq) H

theorem mass_projection (D : LiteralByteProtocol.Decoder) (P : Prover)
    (observe : RawCutProverCompiler.RunView → Rat) :
    lazyMean (projected D (canon P)) emptyTable observe=
      lazyMean (recorded D (build D) (canon P)) emptyTable (fun v=>observe (view v)) :=
  OraclePortPureOutputC7.lazyMean_map _ _ _ _

#print axioms first_reads
#print axioms log_length
#print axioms mass_projection
end AspisR1.F3T_Accounting
end
