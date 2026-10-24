import Port4C_QueryStd
import Port4C_QueryArithmetic
import Port4B_Opening
import R1FoldedLeafCodec
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_OpeningValues
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical MultiproofConeSlices
open OraclePortCompactDraft
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev FE := AspisWideTower.WideExact

def zero : E := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
def values (a : Array E 4#usize) (j : Fin 4) : FE :=
  CheckpointBytes5Output.ofE (a.val[j.val]?.getD zero)

/-- Session A S3's exact strict byte-decoder port, on its own operand slice.
This mentions no parsed proof, query/fold, Prepared or model result. -/
structure SessionAS3 (ops : Ops) : Prop where
  decode : ∀ bytes i value, i.val<4 → bytes.val.length=128 → ops.op21 bytes i=ok value →
    FoldedLeafCodec.decodeWide (slice (bytesOf bytes.val) (32*i.val) 32)=
      some (CheckpointBytes5Output.ofE value)

theorem read (ops : Ops) (decoder : SessionAS3 ops) (opening : Slice U8)
    (size : opening.val.length=832) (i : Usize) (hi : i.val<4) (value : E)
    (run : Port4C_QueryStd.readValue ops opening i=ok value) :
    FoldedLeafCodec.decodeWide
      (slice (slice (bytesOf opening.val) 672 128) (32*i.val) 32)=
        some (CheckpointBytes5Output.ofE value) := by
  have loVal : (672#usize).val=672 := by scalar_tac
  have hiVal : (800#usize).val=800 := by scalar_tac
  have range := range_total opening 672#usize 800#usize (by decide) (by rw [size]; decide)
  unfold Port4C_QueryStd.readValue at run
  rw [range,bind_tc_ok] at run
  have length : (sub opening 672#usize 800#usize).val.length=128 := by
    have h := sub_length opening 672#usize 800#usize (by decide) (by rw [size]; decide)
    rw [loVal,hiVal] at h
    exact h
  have exact := decoder.decode (sub opening 672#usize 800#usize) i value hi length run
  simpa only [bytes_sub,loVal,hiVal] using exact

theorem four (ops : Ops) (decoder : SessionAS3 ops) (opening : Slice U8)
    (size : opening.val.length=832) (out : Array E 4#usize)
    (run : (Port4C_QueryStd.install ops).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (Port4C_QueryStd.install ops)) opening=ok out) :
    FoldedLeafCodec.decodeFolded (slice (bytesOf opening.val) 672 128)=some (values out) := by
  obtain ⟨v0,v1,v2,v3,r0,r1,r2,r3,contents⟩ := Port4C_QueryStd.four_reads ops opening out run
  apply (FoldedLeafCodec.decodeFolded_eq_some_iff _ _).2
  constructor
  · unfold slice bytesOf
    rw [List.length_take,List.length_drop,List.length_map,size]
    rfl
  · intro j
    have h0 := read ops decoder opening size 0#usize (by decide) v0 r0
    have h1 := read ops decoder opening size 1#usize (by decide) v1 r1
    have h2 := read ops decoder opening size 2#usize (by decide) v2 r2
    have h3 := read ops decoder opening size 3#usize (by decide) v3 r3
    fin_cases j
    · simp only [values,contents,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      exact h0
    · simp only [values,contents,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      exact h1
    · simp only [values,contents,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      exact h2
    · simp only [values,contents,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      exact h3

#print axioms read
#print axioms four
end AspisR1.Port5Q1_OpeningValues
end
