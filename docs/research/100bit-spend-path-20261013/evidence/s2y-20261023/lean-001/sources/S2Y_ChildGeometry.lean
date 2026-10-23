import AdapterRwLeadInputs
import MultiproofConeParserTotal

/-! Checked-range transport only. No native child provenance is assumed installed.
Physical slots retain padding; semantic decoded rows are a separate projection. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2Y_ChildGeometry
open Aeneas Aeneas.Std Result
open S2LeadInterface MultiproofConeCanonical OraclePortCompactDraft

/-- A checked source range identifies the actual slice, including its carrier. -/
theorem range_segment (proof actual : Slice U8) (start finish : Usize)
    (ordered : start.val ≤ finish.val) (within : finish.val ≤ proof.val.length)
    (run : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start := start, «end» := finish} = ok actual) :
    actual = S8JoinFrozenScan.segment proof start.val (finish.val-start.val) := by
  apply Subtype.ext
  exact (AdapterRw.Ranges.selected_exact proof actual start finish ordered within run).1

/-- Wire transport for an actual checked range; no address/length substitute. -/
theorem range_wire (proof actual : Slice U8) (start finish : Usize)
    (ordered : start.val ≤ finish.val) (within : finish.val ≤ proof.val.length)
    (run : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start := start, «end» := finish} = ok actual) :
    bytesOf actual.val = slice (bytesOf proof.val) start.val (finish.val-start.val) := by
  rw [range_segment proof actual start finish ordered within run]
  exact S8JoinFrozenScan.segment_wire proof start.val (finish.val-start.val)

/-- A physical slot is a range on the same stored input accepted by C4.
The parser's semantic rows need not equal these physical padded bytes. -/
theorem physical_slot (proof actual : Slice U8) (tr : RawCutTranscriptRun.ErasedPrefix)
    (parsed : Parsed) (parser : OraclePortStoredParserC4.parseReached
      (bytesOf proof.val) tr = some parsed)
    (slot : Nat) (start finish : Usize)
    (at : start.val = OraclePortSelectedDraft.slotStart slot)
    (width : finish.val = start.val + 32*OraclePortSelectedDraft.capacity slot)
    (within : finish.val ≤ proof.val.length)
    (run : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start := start, «end» := finish} = ok actual) :
    bytesOf actual.val = slice parsed.wire (OraclePortSelectedDraft.slotStart slot)
      (32*OraclePortSelectedDraft.capacity slot) := by
  have ordered : start.val ≤ finish.val := by omega
  have size : finish.val-start.val = 32*OraclePortSelectedDraft.capacity slot := by omega
  rw [range_wire proof actual start finish ordered within run, at, size,
    (OraclePortStoredParserC4.parsed _ _ _ parser).2.1]

/-- The reference parser's accepted rows agree with the SAME C4 parsed object. -/
theorem parser_rows (proof : Slice U8) (tr : RawCutTranscriptRun.ErasedPrefix)
    (parsed : Parsed) (rows : alloc.vec.Vec (alloc.vec.Vec U8))
    (parser : OraclePortStoredParserC4.parseReached (bytesOf proof.val) tr = some parsed)
    (reference : MultiproofParserRef.parser_reference.parse proof = ok (some rows)) :
    MultiproofConeParserControl.decodedRows rows = parsed.semantic := by
  obtain ⟨p,hp,_,same⟩ := MultiproofConeParserTotal.accepted_parse proof rows reference
  have eqp : p = parsed := Option.some.inj
    (hp.symm.trans (OraclePortStoredParserC4.parsed _ _ _ parser).1)
  simpa only [eqp] using same

/-- Exact 7031/464 argument and its successful S8 scan, using C4 on same bytes. -/
theorem y1_scan (proof actual : Slice U8) (tr : RawCutTranscriptRun.ErasedPrefix)
    (parsed : Parsed) (parser : OraclePortStoredParserC4.parseReached
      (bytesOf proof.val) tr = some parsed)
    (within : 7495 ≤ proof.val.length)
    (run : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start := 7031#usize, «end» := 7495#usize} = ok actual) :
    actual = S8JoinFrozenScan.segment proof 7031 464 ∧
    S8OwnedP6.check_values_owned actual = ok (.Ok ()) := by
  have same : actual = S8JoinFrozenScan.segment proof 7031 464 := by
    simpa using range_segment proof actual 7031#usize 7495#usize (by decide) within run
  refine ⟨same,?_⟩
  rw [same]
  exact S8JoinFrozenScan.parsed_y1 proof tr parsed parser

#print axioms range_segment
#print axioms range_wire
#print axioms physical_slot
#print axioms parser_rows
#print axioms y1_scan
end AspisR1.S2Y_ChildGeometry
end
