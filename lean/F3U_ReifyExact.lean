import F3U_ReifyLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_ReifyExact
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem exact {A : Type} (code : SdkC_Source.Code A) (H : Bytes → State) :
    eval H (SdkC_Oracle.program code)=
      (SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H) code []).2,
        (SdkC_Source.run (F3U_Oracle.hashv H) code []).1) := by
  apply Prod.ext
  · simpa only [SdkC_Source.readLog,List.filterMap_nil,List.nil_append] using (F3U_ReifyLog.log code H []).symm
  · exact (F3U_ReifyValue.value code H).trans (SdkC_Source.erasure _ code []).symm

#print axioms exact
end AspisR1.F3U_ReifyExact
end
