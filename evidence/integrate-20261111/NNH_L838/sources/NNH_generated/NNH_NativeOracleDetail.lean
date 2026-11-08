import NNH_NativeOracleBatch
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_NativeOracleDetail
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NNH_NativeOracleSlots
variable (H : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)
/-- Preserve the exact entered event, reply, history, abort prefix and native
mutable arrays. No returning-result law or Root0 is used. The dependent window
index of the enclosing occurrence is a separate remaining obligation. -/
def transport {e : NJU_CommonObserved.Event}
 (source : NLT_Subcuts.Detail (part H pda clock r) e) : NLT_Subcuts.Detail H e := by
 cases source with
 | ordinary e notMerkle => exact .ordinary e notMerkle
 | returning pr p folded reply inside out child =>
  exact .returning pr p folded reply inside out
   (NNH_NativeOracleBatch.returning H pda clock r pr p folded 1#usize inside out child)
 | aborting pr p folded error inside pending child =>
  exact .aborting pr p folded error inside pending
   (NNH_NativeOracleBatch.aborting H pda clock r pr p folded 1#usize inside pending child)
#print axioms transport
end AspisR1.NNH_NativeOracleDetail
end
