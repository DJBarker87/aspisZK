import FourDotsCurrentQmParserRootV1
import FourDotsActualTailInputMeaningRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsActualTailParserRootV1
open AspisR1FastDotsCurrentQmParserRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1
open AspisR1FastDotsActualTailBodyTraceRootV1
open AspisR1.RetainedFieldByteCodec

def frame (bytes : Slice U8) (hlen : bytes.val.length=16) : Array U8 16#usize :=
  ⟨bytes.val,by change bytes.val.length=16; exact hlen⟩

theorem frame_to_slice (bytes : Slice U8) (hlen : bytes.val.length=16) :
    Array.to_slice (frame bytes hlen)=bytes := by
  apply Subtype.ext
  rfl

theorem parser_slice_success
    (ops : Ops) (bytes : Slice U8) (q : QM) (optQ : Option QM)
    (hlen : bytes.val.length=16)
    (hbinding : ops.qm31FromBytes=parser)
    (hparse : ops.qm31FromBytes bytes=.ok optQ)
    (hunwrap : core.option.Option.unwrap optQ=.ok q) :
    ∃ limbs : QM31Limbs,
      decodeQM31LE (AspisR1.CandidateParserByteOrder.arrayBytes16 (frame bytes hlen))=some limbs ∧
      q=limbsToCurrent limbs ∧
      encodeQM31LE limbs=AspisR1.CandidateParserByteOrder.arrayBytes16 (frame bytes hlen) ∧
      q.c0.a.val<m31Modulus ∧ q.c0.b.val<m31Modulus ∧
      q.c1.a.val<m31Modulus ∧ q.c1.b.val<m31Modulus := by
  have hp : parser bytes=.ok (some q) := by
    cases optQ with
    | none => simp only [core.option.Option.unwrap,Result.ofOption] at hunwrap; cases hunwrap
    | some value =>
      have hv : value=q := Result.ok.inj hunwrap
      simpa only [hbinding,hv] using hparse
  apply installed_parser_success_strict ops (frame bytes hlen) q
  change parser (Array.to_slice (frame bytes hlen))=.ok (some q)
  rw [frame_to_slice]
  exact hp

/-- Successful actual tail slicing establishes its own sixteen-byte frame. -/
theorem tail_input_frame_length
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (iter iter' : AspisR1FastDotsActualTailBodyTraceRootV1.Range) (old next : Tail) (c : Contribution)
    (hw : InputWitness ops a g slot iter iter' old next c) : c.bytes.val.length=16 := by
  obtain ⟨slot32,base480,term16,offset,coeffIndex,finish,optQ,pushed,u,
    hnext,h0,h1,h2,h3,h4,hread,h5,hslice,hparse,hunwrap,hpush,hunpush,htail⟩ := hw
  have hv : finish.val=offset.val+16 := by scalar_tac
  rw [Array.index_SliceIndexRangeUsizeSlice] at hslice
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at hslice
  split at hslice
  · rename_i hb
    have heq := Result.ok.inj hslice
    have he := congrArg Subtype.val heq
    have hlen : a.val.length=608 := by simpa using a.property
    have hend : finish.val≤608 := by
      have h := hb.2
      simpa only [UScalar.le_equiv,Slice.length,Array.to_slice,hlen] using h
    rw [←he,List.slice_length,hlen,hv]
    have hspan : offset.val+16-offset.val=16 := by omega
    rw [hspan,Nat.min_eq_right (by omega)]
  · cases hslice

/-- Same source witness supplies framing, parser success and canonicality;
only the concrete operation-slot installation is left as a binding premise. -/
theorem tail_input_strict_parser
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (iter iter' : AspisR1FastDotsActualTailBodyTraceRootV1.Range) (old next : Tail) (c : Contribution)
    (hbinding : ops.qm31FromBytes=parser)
    (hw : InputWitness ops a g slot iter iter' old next c) :
    ∃ (hlen : c.bytes.val.length=16) (limbs : QM31Limbs),
      decodeQM31LE (AspisR1.CandidateParserByteOrder.arrayBytes16 (frame c.bytes hlen))=some limbs ∧
      c.scalar=limbsToCurrent limbs ∧
      encodeQM31LE limbs=AspisR1.CandidateParserByteOrder.arrayBytes16 (frame c.bytes hlen) ∧
      c.scalar.c0.a.val<m31Modulus ∧ c.scalar.c0.b.val<m31Modulus ∧
      c.scalar.c1.a.val<m31Modulus ∧ c.scalar.c1.b.val<m31Modulus := by
  have hlen := tail_input_frame_length ops a g slot iter iter' old next c hw
  obtain ⟨slot32,base480,term16,offset,coeffIndex,finish,optQ,pushed,u,
    hnext,h0,h1,h2,h3,h4,hread,h5,hslice,hparse,hunwrap,hpush,hunpush,htail⟩ := hw
  exact ⟨hlen,parser_slice_success ops c.bytes c.scalar optQ hlen hbinding hparse hunwrap⟩
#print axioms parser_slice_success
#print axioms tail_input_frame_length
#print axioms tail_input_strict_parser
end AspisR1FastDotsActualTailParserRootV1
