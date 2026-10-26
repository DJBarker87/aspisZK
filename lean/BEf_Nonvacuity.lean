import BEf_Count
import BEf_Bind
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEf_Nonvacuity
open Aeneas Aeneas.Std Result SdkC_Source

/-- A genuinely rejected call retains its effect and its attempted query. -/
theorem rejected (parts : Parts) (count : Nat) (before : Log) :
    BEf_Carrier.run (BEf_Count.call (fun _ => .fail .panic))
      (SdkC_Source.digestCode parts) count before =
      (.fail .panic,count+1,before ++ [⟨parts,.fail .panic⟩]) := rfl

/-- A successful read followed by a rejected pure operation has no suffix call. -/
theorem rejected_after_read (parts extra : Parts) (digest : Digest)
    (count : Nat) (before : Log) :
    BEf_Carrier.run (BEf_Count.call (fun _ => .ok digest))
      (.read parts (fun _ => .step (.fail .panic : Result Unit)
        (fun _ => SdkC_Source.digestCode extra))) count before =
      (.fail .panic,count+1,before ++ [⟨parts,.ok digest⟩]) := rfl

/-- Repeated identical calls remain distinct effects. -/
theorem repeated (parts : Parts) (digest : Digest) (count : Nat) (before : Log) :
    BEf_Carrier.run (BEf_Count.call (fun _ => .ok digest))
      (.read parts (fun _ => .read parts (fun _ => .done ()))) count before =
      (.ok (),count+2,before ++ [⟨parts,.ok digest⟩,⟨parts,.ok digest⟩]) := by
  simp only [BEf_Carrier.run,BEf_Count.call,List.append_assoc,List.singleton_append]

#print axioms rejected
#print axioms rejected_after_read
#print axioms repeated
end AspisR1.BEf_Nonvacuity
end
