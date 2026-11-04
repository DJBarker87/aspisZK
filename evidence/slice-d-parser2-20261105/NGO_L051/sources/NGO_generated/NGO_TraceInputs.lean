import NGO_ChunksNativeStart
import NGD_DecodeValueLaw
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_TraceInputs
open NGD_DecodeTrace AspisR1DecodeKFullV10
/-- A typed source chunk's low half equals the exact retained decoder input. -/
theorem selected {N : Usize} {r : Record} {off start : Usize}
    (d : Domain N r off start) (original : core.slice.iter.ChunksExact U8)
    (values : original.chunks.map (fun c=>c.val)=
      NGO_ChunkSchedule.windows (((r.framed.val.drop 5).drop (32*off.val)).take (32*N.val)) N.val)
    (length : original.chunks.length=N.val) (index : Usize) (live : index.val<N.val) :
    ((original.chunks[index.val]'(by omega)).val).take 16 =
      (NGD_DecodeValueLaw.input r off N index d.minlen d.cap d.positive live d.range).val := by
  have eq := congrArg (fun xs : List (List U8)=>xs[index.val]?) values
  have idxBound : index.val<original.chunks.length := by omega
  have natBound : index.val<(NGO_ChunkSchedule.windows
    (((r.framed.val.drop 5).drop (32*off.val)).take (32*N.val)) N.val).length := by
    rw [NGO_ChunkSchedule.window_count];exact live
  have atIndex : (original.chunks[index.val]'idxBound).val =
      (NGO_ChunkSchedule.windows (((r.framed.val.drop 5).drop (32*off.val)).take (32*N.val)) N.val)[index.val]'natBound := by
    simp only [List.getElem?_map,List.getElem?_eq_getElem idxBound,
      List.getElem?_eq_getElem natBound,Option.map_some] at eq
    exact Option.some.inj eq
  rw [atIndex,NGO_ChunkSchedule.window_at _ N.val index.val live]
  exact NGD_DecodeGeometry.selected_low (r.framed.val.drop 5) off.val N.val index.val live
#print axioms selected
end NGO_TraceInputs
