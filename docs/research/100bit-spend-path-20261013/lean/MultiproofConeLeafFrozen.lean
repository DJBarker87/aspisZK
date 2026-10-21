import MultiproofConeLeafFold

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeLeafFrozen
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConeLeafFold MultiproofConePhysicalViews
open OraclePortFrozenOrder OraclePortSelectedDraft OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def project : Result (Option reference.Scratch) → Option Live
  | .ok out => out.map (fun t => live t 0 t.n.val)
  | _ => none

/-- Total ordered leaf-program observation equality, including immediate
duplicate disagreement and its exact rejected suffix. The physical step is
the extracted leaf_step, rather than an assumed insertion specification. -/
theorem frozen_join (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (kind : Nat) (ps : List Nat) (s : reference.Scratch)
    (room : s.n.val+ps.length≤16) :
    eval H (bind (leaves p q kind ps s) (fun out => .done (project out))) =
      eval H (hashLeaves p q kind ps (revLive s)) := by
  obtain ⟨log,out,source,target,_⟩ := leaves_join H p q kind ps s room
  have frozen := model_frozen H p q kind ps (revLive s)
  rw [target] at frozen
  rw [eval_bind,source]
  simp only [eval,project,List.append_nil,Option.map_map,Function.comp_def,
    revLive,List.reverse_reverse] at frozen ⊢
  exact frozen

theorem sorted_length (q : Fin 22 → Fin 262144) (batch kind : Nat) :
    (sortedPositions q batch kind).length≤12 := by
  simp only [sortedPositions,List.length_mergeSort,batchPositions]
  split <;> simp

/-- Both frozen batch sizes (10 and 12) start with an empty live prefix.
The unrelated scratch suffix may contain arbitrary data. -/
theorem batch_leaves (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch kind : Nat) (s : reference.Scratch) (empty : s.n.val=0) :
    eval H (bind (leaves p q kind (sortedPositions q batch kind) s)
      (fun out => .done (project out))) =
      eval H (hashLeaves p q kind (sortedPositions q batch kind) []) := by
  have room := sorted_length q batch kind
  have eq := frozen_join H p q kind (sortedPositions q batch kind) s (by omega)
  simpa only [revLive,empty,live_empty,List.reverse_nil] using eq

#print axioms frozen_join
#print axioms sorted_length
#print axioms batch_leaves
end AspisR1.MultiproofConeLeafFrozen
end
