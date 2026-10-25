import AuS1_Prepare
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Observe
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode AuS1_Association

 theorem append (a b : SdkC_Source.Log) :
    SdkC_Source.readLog (a ++ b) = SdkC_Source.readLog a ++ SdkC_Source.readLog b :=
  List.filterMap_append

/-- All-outcome observation equality. Unsuccessful attempts remain in the
native attempt log; only returning reads enter the ROM observation. -/
 theorem lower (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) {A : Type}
    (p : Code A) (association : Uniform hashv p) (before : SdkC_Source.Log) :
    SdkC_Source.readLog (SdkC_Source.run hashv (SdkD_PrepareLower.lower p) before).2 =
      SdkC_Source.readLog before ++ observe (run p).1 := by
  induction p generalizing before with
  | done a => simp only [SdkD_PrepareLower.lower,SdkC_Source.run,run,observe,List.flatMap_nil,List.append_nil]
  | step r next ih => cases r with
    | ok a => exact ih a (association a) before
    | fail e => simp only [SdkD_PrepareLower.lower,SdkC_Source.run,run,observe,List.flatMap_nil,List.append_nil]
    | div => simp only [SdkD_PrepareLower.lower,SdkC_Source.run,run,observe,List.flatMap_nil,List.append_nil]
  | digest D hash parts next ih =>
    cases reply : hashv parts with
    | ok a =>
      simp only [SdkD_PrepareLower.lower,SdkC_Source.run,reply,run,association.1]
      rw [ih a (association.2 a),append]
      simp only [SdkC_Source.readLog,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,observe,
        List.flatMap_cons,List.singleton_append,List.append_assoc]
    | fail e =>
      simp only [SdkD_PrepareLower.lower,SdkC_Source.run,reply,run,association.1,append,
        SdkC_Source.readLog,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,observe,List.flatMap_cons,
        List.flatMap_nil,List.append_nil,List.nil_append]
    | div =>
      simp only [SdkD_PrepareLower.lower,SdkC_Source.run,reply,run,association.1,append,
        SdkC_Source.readLog,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,observe,List.flatMap_cons,
        List.flatMap_nil,List.append_nil,List.nil_append]

#print axioms append
#print axioms lower
end AspisR1.AuS1_Observe
end
