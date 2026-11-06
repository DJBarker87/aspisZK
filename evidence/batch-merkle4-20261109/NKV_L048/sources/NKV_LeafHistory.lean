import NKV_LeafBuild
set_option autoImplicit false
noncomputable section
namespace NKV_LeafHistory
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SqueezeOracleBridge
abbrev HashState := AspisV8R19.SourceDuplexStep.State

def requests (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (kind : Nat) (positions : List Nat) : NKV_LeafBuild.History :=
 positions.map (fun pos => (OraclePortSelectedDraft.leaf p kind pos,
   H (OraclePortSelectedDraft.leaf p kind pos)))

/-- Every result, including a rejected duplicate or abort, has an exact ordered
prefix of the SAME sorted-position requests. No counterfactual suffix query. -/
theorem prefix (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (kind : Nat) (positions : List Nat) (s : reference.Scratch) :
 ∃ remaining,(NKV_LeafBuild.build H p q kind positions s).1++remaining=requests H p kind positions := by
 induction positions generalizing s with
 | nil => exact ⟨[],rfl⟩
 | cons pos rest ih =>
   cases step : reference.leaf_step s (MultiproofConeLeafFold.key q kind pos)
       (encodeState (H (OraclePortSelectedDraft.leaf p kind pos))) with
   | fail e => exact ⟨requests H p kind rest,by simp [NKV_LeafBuild.build,step,requests]⟩
   | div => exact ⟨requests H p kind rest,by simp [NKV_LeafBuild.build,step,requests]⟩
   | ok out =>
     cases out with
     | none => exact ⟨requests H p kind rest,by simp [NKV_LeafBuild.build,step,requests]⟩
     | some t =>
       obtain ⟨remaining,joined⟩:=ih t
       exact ⟨remaining,by simpa only [NKV_LeafBuild.build,step,requests,List.map_cons,List.cons_append]
         using congrArg (List.cons (OraclePortSelectedDraft.leaf p kind pos,
           H (OraclePortSelectedDraft.leaf p kind pos))) joined⟩

theorem complete (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (kind : Nat) (positions : List Nat) (s after : reference.Scratch)
 (accepted : (NKV_LeafBuild.build H p q kind positions s).2=ok (true,after)) :
 (NKV_LeafBuild.build H p q kind positions s).1=requests H p kind positions := by
 induction positions generalizing s with
 | nil => rfl
 | cons pos rest ih =>
   cases step : reference.leaf_step s (MultiproofConeLeafFold.key q kind pos)
       (encodeState (H (OraclePortSelectedDraft.leaf p kind pos))) with
   | fail e => simp [NKV_LeafBuild.build,step] at accepted
   | div => simp [NKV_LeafBuild.build,step] at accepted
   | ok out =>
     cases out with
     | none => simp [NKV_LeafBuild.build,step] at accepted
     | some t =>
       have tail : (NKV_LeafBuild.build H p q kind rest t).2=ok (true,after) := by
         simpa only [NKV_LeafBuild.build,step] using accepted
       simpa only [NKV_LeafBuild.build,step,requests,List.map_cons] using
         congrArg (List.cons (OraclePortSelectedDraft.leaf p kind pos,
           H (OraclePortSelectedDraft.leaf p kind pos))) (ih t tail)

#print prefix
#print complete
#print axioms prefix
#print axioms complete
end NKV_LeafHistory
end
