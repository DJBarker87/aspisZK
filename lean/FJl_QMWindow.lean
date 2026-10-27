import FJl_QMSliceValue
import PSem_Slices
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_QMWindow
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm)
/-- A successful checked sixteen-byte window has its exact literal value. -/
theorem value (q : Array U8 608#usize) (start stop : Usize) (s : Slice U8)
    (o : Option NQ) (v : NQ) (width : stop.val=start.val+16) (bound : stop.val≤608)
    (range : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice U8)) q {start,«end»:=stop}=ok s)
    (parse : FIp_DotDecode.field.QM31.from_le_bytes s=ok o)
    (unwrap : core.option.Option.unwrap o=ok v) :
    ExactLeafFieldCodec.decodeQM31
      (OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf q.val) start.val 16)=some (decodeQM (qm v)) := by
  cases o with
  | none => cases unwrap
  | some x =>
    cases Result.ok.inj unwrap
    have bytes := PSem_Slices.range_bytes (Array.to_slice q) s start stop range
    have w : stop.val-start.val=16 := by omega
    rw [w] at bytes
    have size : s.val.length=16 := by
      rw [bytes,List.length_take,List.length_drop]
      have qlen : q.val.length=608 := q.property
      change min 16 (q.val.length-start.val)=16
      rw [qlen]
      omega
    have h := FJl_QMSliceValue.value s v size parse
    rw [bytes] at h
    simpa only [MultiproofConeCanonical.bytesOf,List.map_take,List.map_drop,Array.to_slice,
      OraclePortCompactDraft.slice] using h
#print axioms value
end AspisR1.FJl_QMWindow
end
