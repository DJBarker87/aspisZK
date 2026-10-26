import NP6_ClaimsRun
import ExtractedPrefixParse
import ExtractedSourceFull25Frames

/-! Derive the exact record width used by the whole-body Kani gates from the
actual successful parser and validated getter on the same prefix. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NP6_RecordShape
open Aeneas Aeneas.Std Result
namespace R := AspisR1PrefixAggregateParser.r1_wire

private theorem checked {ty : UScalarTy} (x : UScalar ty) :
    UScalar.tryMk ty x.val = ok x := by
  have bounds : UScalar.check_bounds ty x.val = true := by
    simpa only [UScalar.check_bounds,decide_eq_true_eq] using x.hBounds
  simp only [UScalar.tryMk,UScalar.tryMkOpt,bounds,_root_.dite_true,Result.ofOption]
  congr 1

private theorem add (a b c : Usize) (h : a.val+b.val=c.val) : a+b=ok c := by
  change UScalar.tryMk _ (a.val+b.val)=ok c
  rw [h]
  exact checked c

private theorem mul (a b c : Usize) (h : a.val*b.val=c.val) : a*b=ok c := by
  change UScalar.tryMk _ (a.val*b.val)=ok c
  rw [h]
  exact checked c

theorem shape25 : R.row_shape 25#u8 = ok (some (4#u8,3712#usize)) := by
  have claims : R.CLAIMS=ok 87#usize := by
    unfold R.CLAIMS R.POINTS R.LANES
    exact mul _ _ _ rfl
  have plus : 87#usize+29#usize=ok 116#usize := add _ _ _ rfl
  have times : 116#usize*32#usize=ok 3712#usize := mul _ _ _ rfl
  simp only [R.row_shape,claims,R.LANES,bind_tc_ok,plus,times]

theorem record25_length (frame payload : Slice U8)
    (parsed : R.parse_record 25#u8 frame = ok (.Ok payload)) :
    frame.val.length = 3717 := by
  unfold R.parse_record at parsed
  rw [shape25] at parsed
  simp only [bind_tc_ok,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch] at parsed
  have summed : 5#usize+3712#usize=ok 3717#usize := add _ _ _ rfl
  rw [summed] at parsed
  simp only [bind_tc_ok] at parsed
  have length : Slice.len frame=3717#usize := by
    by_contra different
    simp [different] at parsed
  exact congrArg UScalar.val length

theorem on_parsed_prefix (bytes : Slice U8)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
    (parsed : AspisR1PublicPreparation.PrefixAdapter.parseAccepted bytes = ok (.Ok pre))
    (called : AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 25#u8 = ok (.Ok record)) :
    record.framed.val.length = 3717 := by
  have hp := AspisR1PublicPreparation.PrefixAdapter.parse_success bytes pre parsed
  obtain ⟨_,slot⟩ := AspisR1PublicPreparation.SourceFull25.validated_record_bytes pre 25#u8 record called
  have mem : (25#u8,record.framed) ∈ AspisR1.ExtractedPrefixTrace.rowOrder.zip
      (AspisR1PublicPreparation.PrefixAdapter.toOld pre).records.val := by
    apply List.mem_of_getElem? (i:=25)
    apply List.getElem?_zip_eq_some.mpr
    exact ⟨rfl,slot⟩
  obtain ⟨payload,hrecord⟩ := AspisR1.ExtractedPrefixParse.parse_record_of_success bytes
    (AspisR1PublicPreparation.PrefixAdapter.toOld pre) hp 25#u8 record.framed mem
  exact record25_length record.framed payload hrecord

#print axioms checked
#print axioms add
#print axioms mul
#print axioms shape25
#print axioms record25_length
#print axioms on_parsed_prefix
end AspisR1.NP6_RecordShape
end
