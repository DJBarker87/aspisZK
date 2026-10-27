import BEf_Fold
import BEf_Offset
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEf_Count
open Aeneas Aeneas.Std Result SdkC_Source

def call (hashv : Parts → Result Digest) (parts : Parts) (count : Nat) :=
  (hashv parts,count+1)

theorem replay (hashv : Parts → Result Digest) (log : Log) (count : Nat) :
    BEf_Fold.replay (call hashv) log count = count + log.length := by
  induction log generalizing count with
  | nil => rfl
  | cons q rest ih =>
    simp only [BEf_Fold.replay,call,ih,List.length_cons]
    omega

/-- Counts every attempted syscall, on accepted or rejected runs. -/
theorem exact {A : Type} (hashv : Parts → Result Digest) (code : Code A)
    (count : Nat) (before : Log) :
    BEf_Carrier.run (call hashv) code count before =
      ((SdkC_Source.run hashv code []).1,
       count + (SdkC_Source.run hashv code []).2.length,
       before ++ (SdkC_Source.run hashv code []).2) := by
  have projected := BEf_Carrier.source (call hashv) hashv (fun _ _ => rfl) code count before
  have offset := BEf_Offset.source hashv code before
  obtain ⟨suffix,logs,state⟩ := BEf_Fold.carrier (call hashv) code count before
  have sameLog : before ++ suffix = before ++ (SdkC_Source.run hashv code []).2 :=
    logs.symm.trans ((congrArg Prod.snd projected).trans (congrArg Prod.snd offset))
  have same : suffix = (SdkC_Source.run hashv code []).2 := List.append_cancel_left sameLog
  apply Prod.ext
  · exact (congrArg Prod.fst projected).trans (congrArg Prod.fst offset)
  · exact Prod.ext (by rw [state,replay,same]) (logs.trans (congrArg (before ++ ·) same))

#print axioms replay
#print axioms exact
end AspisR1.BEf_Count
end
