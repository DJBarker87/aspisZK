import NFB_PrivateFrame
import NFB_GatherChain
set_option autoImplicit false
namespace NFB_GatherFrame
open Aeneas.Std NFB_PhysicalFrame NFB_PrivateFrame NFB_GatherTrace

def actions : List Row → List Action
 | [] => []
 | r::rs => append .flat r.words :: append .lines [r.lineZ] :: actions rs

theorem owned (rows : List Row) : ∀ a∈actions rows, Private a := by
 induction rows with
 | nil => simp [actions]
 | cons r rs ih =>
  intro a ha
  simp only [actions,List.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · exact Private.append _ _
  · exact Private.append _ _
  · exact ih a ha

theorem query_frame (rows : List Row) (heap : Heap) (count : Nat) :
 run ((actions rows).take count) heap 0=heap 0 :=
 protected_query (actions rows) heap count (owned rows)

/-- The ordered two-owner writes reconstruct both buffers in the SAME heap. -/
theorem payloads (rows : List Row) (heap : Heap) (flat lines : List U32)
 (hflat : heap Place.flat.id=some flat) (hlines : heap Place.lines.id=some lines) :
 run (actions rows) heap Place.flat.id=some (flat++rows.flatMap (fun r=>r.words)) ∧
 run (actions rows) heap Place.lines.id=some (lines++rows.map (fun r=>r.lineZ)) := by
 induction rows generalizing heap flat lines with
 | nil => simp [actions,NFB_PhysicalFrame.run,hflat,hlines]
 | cons r rs ih =>
  let next := (append .lines [r.lineZ]).apply ((append .flat r.words).apply heap)
  have hf : next Place.flat.id=some (flat++r.words) := by
   simp only [Place.id] at hflat
   simp [next,append,Action.apply,write,Place.id,hflat]
  have hl : next Place.lines.id=some (lines++[r.lineZ]) := by
   simp only [Place.id] at hlines
   simp [next,append,Action.apply,write,Place.id,hlines]
  have result := ih next (flat++r.words) (lines++[r.lineZ]) hf hl
  simpa [actions,NFB_PhysicalFrame.run,next,List.flatMap_cons,List.map_cons,List.append_assoc] using result
#print axioms owned
#print axioms query_frame
#print axioms payloads
end NFB_GatherFrame
