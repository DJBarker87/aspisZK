import AspisR1FastDotsCurrent.FunsOpsV4
import ActualDecodeKStrictQM31Parser
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsCurrentQmParserRootV1
open AspisR1.RetainedFieldByteCodec
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev QM := AspisR1FastDotsCurrent.aspis_core.field.QM31
abbrev ActualQ := AspisR1.ActualDecodeKFieldParserTransport.ActualQ

def toCurrent (q : ActualQ) : QM :=
  {c0:={a:=q.c0.a,b:=q.c0.b},c1:={a:=q.c1.a,b:=q.c1.b}}

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok a => .ok (f a)
  | .fail e => .fail e
  | .div => .div

def parser (bytes : Slice U8) : Result (Option QM) :=
  mapResult (Option.map toCurrent)
    (AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes bytes)

def limbsToCurrent (limbs : QM31Limbs) : QM :=
  toCurrent (AspisR1.ActualDecodeKStrictQM31Parser.limbsToActual limbs)

def withCurrentQmParser (ops : Ops) : Ops := {ops with qm31FromBytes:=parser}

theorem parser_binding (ops : Ops) : (withCurrentQmParser ops).qm31FromBytes=parser := rfl

/-- Concrete source decoder plus literal nominal rewrapping is total on every
fixed sixteen-byte input, including noncanonical inputs rejected by None. -/
theorem parser_fixed_total (bytes : Array U8 16#usize) :
    parser (Array.to_slice bytes) = .ok
      ((decodeQM31LE (AspisR1.CandidateParserByteOrder.arrayBytes16 bytes)).map limbsToCurrent) := by
  unfold parser
  rw [AspisR1.ActualDecodeKStrictQM31Parser.source_refines]
  rfl

theorem limbsToCurrent_values (limbs : QM31Limbs) :
    (limbsToCurrent limbs).c0.a.val=(limbs 0).val ∧
    (limbsToCurrent limbs).c0.b.val=(limbs 1).val ∧
    (limbsToCurrent limbs).c1.a.val=(limbs 2).val ∧
    (limbsToCurrent limbs).c1.b.val=(limbs 3).val := by
  change (AspisR1.M31ParserRefinement.valueToU32 (limbs 0)).val=_ ∧
    (AspisR1.M31ParserRefinement.valueToU32 (limbs 1)).val=_ ∧
    (AspisR1.M31ParserRefinement.valueToU32 (limbs 2)).val=_ ∧
    (AspisR1.M31ParserRefinement.valueToU32 (limbs 3)).val=_
  exact ⟨AspisR1.M31ParserRefinement.valueToU32_val _,
    AspisR1.M31ParserRefinement.valueToU32_val _,
    AspisR1.M31ParserRefinement.valueToU32_val _,
    AspisR1.M31ParserRefinement.valueToU32_val _⟩

/-- A successful installed source parser yields canonical retained limbs of
the exact same input bytes and their strict encoding roundtrip. -/
theorem installed_parser_success_strict
    (ops : Ops) (bytes : Array U8 16#usize) (q : QM)
    (h : (withCurrentQmParser ops).qm31FromBytes (Array.to_slice bytes) = .ok (some q)) :
    ∃ limbs : QM31Limbs,
      decodeQM31LE (AspisR1.CandidateParserByteOrder.arrayBytes16 bytes)=some limbs ∧
      q=limbsToCurrent limbs ∧
      encodeQM31LE limbs=AspisR1.CandidateParserByteOrder.arrayBytes16 bytes ∧
      q.c0.a.val<m31Modulus ∧ q.c0.b.val<m31Modulus ∧
      q.c1.a.val<m31Modulus ∧ q.c1.b.val<m31Modulus := by
  change parser (Array.to_slice bytes)=.ok (some q) at h
  rw [parser_fixed_total] at h
  cases hd : decodeQM31LE (AspisR1.CandidateParserByteOrder.arrayBytes16 bytes) with
  | none => simp only [hd,Option.map_none] at h; cases h
  | some limbs =>
      have heq : limbsToCurrent limbs=q := by
        simpa only [hd,Option.map_some,Result.ok.injEq,Option.some.injEq] using h
      have hvalues := limbsToCurrent_values limbs
      refine ⟨limbs,hd,heq.symm,encodeQM31LE_of_decodeQM31LE _ _ hd,?_,?_,?_,?_⟩
      · rw [←heq,hvalues.1]; exact (limbs 0).isLt
      · rw [←heq,hvalues.2.1]; exact (limbs 1).isLt
      · rw [←heq,hvalues.2.2.1]; exact (limbs 2).isLt
      · rw [←heq,hvalues.2.2.2]; exact (limbs 3).isLt
#print axioms parser_fixed_total
#print axioms limbsToCurrent_values
#print axioms installed_parser_success_strict
end AspisR1FastDotsCurrentQmParserRootV1
