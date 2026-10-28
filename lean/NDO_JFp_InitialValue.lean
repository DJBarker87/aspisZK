import NDO_JFr_EncodedCell
import NDO_JFr_BlockWindow
import NDO_JFr_RecordsAt
import NDO_JFr_Data00
import NDO_JFw_NativeRow14
import NDO_JFv_SemanticDecode
set_option autoImplicit false
namespace AspisR1.JFp_InitialValue
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren AspisS1NativeCompact

def record : r1_wire.ValidatedRecord := ⟨14#u8,JFw_NativeRow14.record⟩
def cell : Array U8 16#usize := ⟨JFz_Scan47.b00,by rfl⟩
def limbs : QM31Limbs := ![⟨73778079,by change 73778079<2147483647;omega⟩,
  ⟨1547969474,by change 1547969474<2147483647;omega⟩,
  ⟨1813495781,by change 1813495781<2147483647;omega⟩,
  ⟨1947321224,by change 1947321224<2147483647;omega⟩]
def running : MainQM := genToMain JFr_Data00.running
def values : Array MainQM 1#usize := ⟨[running],by rfl⟩

theorem encoded : CandidateParserByteOrder.arrayBytes16 cell=encodeQM31LE limbs := by
  funext i
  fin_cases i <;> rfl

theorem parser : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell)=
    ok (some (ActualDecodeKStrictQM31Parser.limbsToActual limbs)) :=
  JFr_EncodedCell.parser cell limbs encoded

theorem window : ((record.framed.val.drop 5).drop (32*0)).take 16=cell.val := by
  change (((JFw_Blocks.blocks 1 (JFw_Frames.window 155 16).val).flatten).drop (32*0)).take 16=cell.val
  have selected : (JFw_Frames.window 155 16).val=cell.val := JFz_Scan47.b00_selected
  rw [selected,JFr_BlockWindow.source 1 cell.val (by rfl) 0 (by omega)]
  rfl

theorem source (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
      JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    r1_wire.Prefix.validated_record pre 14#u8=ok (.Ok record) ∧
    decodeMain 1#usize record 0#usize=ok (.Ok values) ∧
    Array.index_usize values 0#usize=ok running := by
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have read := JFr_RecordsAt.source pre records 14#u8 (by change 14<27;omega)
    JFw_NativeRow14.record (by rfl)
  obtain ⟨vr,out,old,call⟩ := JFv_SemanticDecode.initial expanded pre parse
  have same : vr=record := (core.result.Result.Ok.inj (Result.ok.inj (old.symm.trans read)))
  subst vr
  have one := JFr_DecodeCell.source record out call ⟨0,by change 0<1;omega⟩ cell (ActualDecodeKStrictQM31Parser.limbsToActual limbs) window parser
  have cellSame : out.val[0]'(by rw [out.property];change 0<1;omega)=running := one
  have arraySame : out=values := by
    apply Subtype.ext
    apply List.ext_getElem
    · rw [out.property,values.property]
    · intro i hi hj
      have zero : i=0 := by rw [out.property] at hi;change i<1 at hi;omega
      subst i
      exact cellSame
  refine ⟨read,arraySame ▸ call,?_⟩
  rfl

#print axioms encoded
#print axioms parser
#print axioms window
#print axioms source
end AspisR1.JFp_InitialValue
