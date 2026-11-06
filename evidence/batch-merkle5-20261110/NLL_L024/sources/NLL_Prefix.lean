import NLL_LoopHistory
import NLL_AbortInvocation
set_option autoImplicit false
noncomputable section
namespace NLL_Prefix
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

def At (log answered : NLL.History) (parts : Slice (Slice U8)) : Prop :=
 log.take answered.length=answered ∧ (log[answered.length]?).map Prod.fst=some (flatten parts)

theorem cons (head : Bytes × State) (log answered : NLL.History) (parts : Slice (Slice U8))
 (prior : At log answered parts) : At (head::log) (head::answered) parts := by
 constructor
 · simpa only [List.length_cons,List.take_succ_cons] using congrArg (List.cons head) prior.1
 · simpa only [List.length_cons,List.getElem?_cons_succ] using prior.2

theorem next (H : Bytes → State) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
 (batch : Nat) (kind : Usize) (nodes : Slice U8) (root : NLL.Root) (pos : Nat) (rest : List Nat)
 (s t : reference.Scratch)
 (step : reference.leaf_step s (MultiproofConeLeafFold.key q kind.val pos)
     (encodeState (H (OraclePortSelectedDraft.leaf p kind.val pos)))=ok (some t)) :
 NLL_LoopHistory.expected H p q batch kind nodes root (pos::rest) s=
 (OraclePortSelectedDraft.leaf p kind.val pos,H (OraclePortSelectedDraft.leaf p kind.val pos))::
 NLL_LoopHistory.expected H p q batch kind nodes root rest t := by
 simp only [NLL_LoopHistory.expected,NKV_LeafBuild.build,step,List.cons_append]

theorem first (H : Bytes → State) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
 (batch : Nat) (kind : Usize) (nodes : Slice U8) (root : NLL.Root) (pos : Nat) (rest : List Nat)
 (s : reference.Scratch) (parts : Slice (Slice U8)) (address : flatten parts=OraclePortSelectedDraft.leaf p kind.val pos) :
 At (NLL_LoopHistory.expected H p q batch kind nodes root (pos::rest) s) [] parts := by
 unfold At NLL_LoopHistory.expected
 cases step : reference.leaf_step s (MultiproofConeLeafFold.key q kind.val pos)
     (encodeState (H (OraclePortSelectedDraft.leaf p kind.val pos))) with
 | fail e => simp only [NKV_LeafBuild.build,step,List.append_nil,List.length_nil,List.take_zero,List.getElem?_cons_zero,Option.map_some,address];exact ⟨True.intro,True.intro⟩
 | div => simp only [NKV_LeafBuild.build,step,List.append_nil,List.length_nil,List.take_zero,List.getElem?_cons_zero,Option.map_some,address];exact ⟨True.intro,True.intro⟩
 | ok out => cases out with
   | none => simp only [NKV_LeafBuild.build,step,List.append_nil,List.length_nil,List.take_zero,List.getElem?_cons_zero,Option.map_some,address];exact ⟨True.intro,True.intro⟩
   | some t => simp only [NKV_LeafBuild.build,step,List.cons_append,List.length_nil,List.take_zero,List.getElem?_cons_zero,Option.map_some,address];exact ⟨True.intro,True.intro⟩

#print axioms cons
#print axioms next
#print axioms first
end NLL_Prefix
end
