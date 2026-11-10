-- PCVN_ item (1) op2: deployed from_le_bytes slot (NJC_ClosedCalls.inactive) against the frozen wide parser.
import Aeneas
import RPz7_FIo_Install
import NJC_ClosedCalls
import PRVEq_PCVH_R1CandidateWideParserSource_k1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVN_Op2
open AspisR1

-- the deployed slot unfolds to the FIo_Native emission with the retained coordinate port
theorem inactive_def (bytes : Slice Std.U8) :
    NJC_ClosedCalls.inactive bytes = (do
      let decoded ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes
      ok (Option.map FIo_Install.fromE decoded)) := rfl
#print axioms inactive_def
#check @FIo_Install.fromE
#check @FIo_Native.aspis_core.field.wide_exact.WideExact
#check @AspisR1CandidateParser.field.wide_exact.WideExact
#print FIo_Native.aspis_core.field.wide_exact.WideExact
#print AspisR1CandidateParser.field.wide_exact.WideExact
#print FIo_Native.aspis_core.field.QM31
#print AspisR1CandidateParser.field.QM31
end PCVN_Op2
