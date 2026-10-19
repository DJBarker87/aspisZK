import ExtractedSourceFull25Frames

/-! Index views of the same actual Call trace. stateAt carries the actual
SemanticTranscript objects; it introduces no independent state witness. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SourceTraceIndices
open r1_wire

def stateAt {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (start : SemanticTranscript Hash) (cs : List (SourceFull25.Call D pre))
    (index : Nat) : SemanticTranscript Hash :=
  match index, cs with
  | 0, _ => start
  | _ + 1, [] => start
  | n + 1, c :: tail => stateAt c.after tail n

theorem zero {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (start : SemanticTranscript Hash) (cs : List (SourceFull25.Call D pre)) :
    stateAt start cs 0 = start := by
  cases cs <;> rfl

theorem get_after {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (start : SemanticTranscript Hash) (cs : List (SourceFull25.Call D pre))
    (index : Nat) (c : SourceFull25.Call D pre) (hc : cs[index]? = some c) :
    stateAt start cs (index + 1) = c.after := by
  induction cs generalizing start index with
  | nil => simp at hc
  | cons head tail ih =>
    cases index with
    | zero =>
      change some head = some c at hc
      cases Option.some.inj hc
      simpa only [Nat.zero_add, stateAt] using zero c.after tail
    | succ index =>
      change tail[index]? = some c at hc
      simpa only [stateAt] using ih head.after index hc

theorem get_before {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    {start finish : SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (run : SourceFull25.Trace D pre start finish cs)
    (index : Nat) (c : SourceFull25.Call D pre) (hc : cs[index]? = some c) :
    stateAt start cs index = c.before := by
  induction run generalizing index with
  | nil self => simp at hc
  | cons head tail ih =>
    cases index with
    | zero =>
      change some head = some c at hc
      cases Option.some.inj hc
      rfl
    | succ index =>
      simpa only [stateAt] using ih index hc

theorem endpoint {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    {start finish : SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (run : SourceFull25.Trace D pre start finish cs) :
    stateAt start cs cs.length = finish := by
  induction run with
  | nil self => rfl
  | cons head tail ih => simpa only [List.length_cons, stateAt] using ih

theorem adjacent {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    {start finish : SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (run : SourceFull25.Trace D pre start finish cs)
    (index : Nat) (c next : SourceFull25.Call D pre)
    (hc : cs[index]? = some c) (hn : cs[index + 1]? = some next) :
    c.after = next.before :=
  (get_after start cs index c hc).symm.trans (get_before run (index + 1) next hn)

theorem length_of_rows {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (cs : List (SourceFull25.Call D pre)) (count : Nat)
    (rows : cs.map (fun c => c.row.val) = List.range count) : cs.length = count := by
  simpa only [List.length_map, List.length_range] using congrArg List.length rows

theorem row_index {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (cs : List (SourceFull25.Call D pre)) (count : Nat)
    (rows : cs.map (fun c => c.row.val) = List.range count)
    (index : Nat) (c : SourceFull25.Call D pre) (hc : cs[index]? = some c) :
    c.row.val = index := by
  obtain ⟨hi, hvalue⟩ := List.getElem?_eq_some_iff.mp hc
  have hlen := length_of_rows cs count rows
  have hin : index < count := by omega
  have hl : (cs.map (fun c => c.row.val))[index]? = some c.row.val := by
    rw [List.getElem?_map, hc]
    rfl
  have hr := List.getElem?_range hin
  have he := congrArg (fun values : List Nat => values[index]?) rows
  exact Option.some.inj (hl.symm.trans (he.trans hr))

theorem endpoint_of_rows {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    {start finish : SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (run : SourceFull25.Trace D pre start finish cs) (count : Nat)
    (rows : cs.map (fun c => c.row.val) = List.range count) :
    stateAt start cs count = finish := by
  rw [← length_of_rows cs count rows]
  exact endpoint run

#print axioms stateAt
#print axioms zero
#print axioms get_after
#print axioms get_before
#print axioms endpoint
#print axioms adjacent
#print axioms length_of_rows
#print axioms row_index
#print axioms endpoint_of_rows
end AspisR1PublicPreparation.SourceTraceIndices
