import SCH_OuterTrace
import SCH_CollisionKnownSuffix
import SCG_Nonvacuity
set_option autoImplicit false
namespace AspisR1.SCH_Nonvacuity
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- The unconditional interpreter and collision lemmas have simultaneous
inhabitants in every world. Crypto-native acceptance is not claimed here;
SCG_Nonvacuity.joint retains the independent actual bank/wrapper fixture. -/
theorem interpretation {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State) :
    (eval H (SdkC_Oracle.program (GExq_OuterLower.lower
      (SCH_OuterIdealLog.child c hashv) (S2W_Trace.Code.done ())))).2 = ok () ∧
    ∃ log, S2W_Trace.run (SCH_IdealSdk.dictionary c hashv H) (.done ()) [] = ok ((),log) ∧
      SCH_OuterIdealLog.trace c hashv H log = [] := ⟨rfl,[],rfl,rfl⟩

#print axioms interpretation
#check AspisR1.SCG_Nonvacuity.joint
#print axioms AspisR1.SCG_Nonvacuity.joint
end AspisR1.SCH_Nonvacuity
