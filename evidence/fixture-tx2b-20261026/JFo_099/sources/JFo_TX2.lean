import JFo_Opening10_0
import JFo_Opening10_1
import JFo_Opening10_2
import JFo_Opening10_3
import JFo_Opening11_0
import JFo_Opening11_1
import JFo_Opening11_2
import JFo_Opening11_3
import JFo_Opening12_0
import JFo_Opening12_1
import JFo_Opening12_2
import JFo_Opening12_3
import JFo_Opening13_0
import JFo_Opening13_1
import JFo_Opening13_2
import JFo_Opening13_3
import JFo_Opening14_0
import JFo_Opening14_1
import JFo_Opening14_2
import JFo_Opening14_3
import JFo_Opening15_0
import JFo_Opening15_1
import JFo_Opening15_2
import JFo_Opening15_3
import JFo_Opening16_0
import JFo_Opening16_1
import JFo_Opening16_2
import JFo_Opening16_3
import JFo_Opening17_0
import JFo_Opening17_1
import JFo_Opening17_2
import JFo_Opening17_3
import JFo_Opening18_0
import JFo_Opening18_1
import JFo_Opening18_2
import JFo_Opening18_3
import JFo_Opening19_0
import JFo_Opening19_1
import JFo_Opening19_2
import JFo_Opening19_3
import JFo_Opening20_0
import JFo_Opening20_1
import JFo_Opening20_2
import JFo_Opening20_3
import JFo_Opening21_0
import JFo_Opening21_1
import JFo_Opening21_2
import JFo_Opening21_3
import JFo_ResumeNative
import JFo_Pending
import JFo_Powers
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_QueryFixture
open Aeneas Aeneas.Std Result

def position (i : Fin 12) : Fin 22 := ⟨10+i.val,by have := i.isLt;omega⟩
def slot (j : Fin 4) : Usize := Usize.ofNat j.val (by have := j.isLt;scalar_tac)

/-- Exact source decoder calls installed in TX2 on the SAME real proof openings.
This proves the four field reads at each remaining query; folding comparisons,
row updates, batch1, post-query flush and finish acceptance are still open. -/
theorem decoded (seed : Port3_NativeQueryBody.Ops) (i : Fin 12) :
    ∃ values : Fin 4 → SAQ_WideABI.E, ∀ j : Fin 4,
      (Port4C_RowStd.install (Port5Q1_QueryPorts.install (SAQ_Decoder.install seed))).op21
        (JFo_Opening.value (position i)) (slot j)=ok (values j) := by
  change ∃ values : Fin 4 → SAQ_WideABI.E, ∀ j : Fin 4,
    SAQ_Decoder.read (JFo_Opening.value (position i)) (slot j)=ok (values j)
  fin_cases i
  · refine ⟨![SAQ_RecordDecode.fromRecord JFo_Opening10_0.value,SAQ_RecordDecode.fromRecord JFo_Opening10_1.value,SAQ_RecordDecode.fromRecord JFo_Opening10_2.value,SAQ_RecordDecode.fromRecord JFo_Opening10_3.value],?_⟩
    intro j
    fin_cases j
    · exact JFo_Opening10_0.source
    · exact JFo_Opening10_1.source
    · exact JFo_Opening10_2.source
    · exact JFo_Opening10_3.source
  · refine ⟨![SAQ_RecordDecode.fromRecord JFo_Opening11_0.value,SAQ_RecordDecode.fromRecord JFo_Opening11_1.value,SAQ_RecordDecode.fromRecord JFo_Opening11_2.value,SAQ_RecordDecode.fromRecord JFo_Opening11_3.value],?_⟩
    intro j
    fin_cases j
    · exact JFo_Opening11_0.source
    · exact JFo_Opening11_1.source
    · exact JFo_Opening11_2.source
    · exact JFo_Opening11_3.source
  · refine ⟨![SAQ_RecordDecode.fromRecord JFo_Opening12_0.value,SAQ_RecordDecode.fromRecord JFo_Opening12_1.value,SAQ_RecordDecode.fromRecord JFo_Opening12_2.value,SAQ_RecordDecode.fromRecord JFo_Opening12_3.value],?_⟩
    intro j
    fin_cases j
    · exact JFo_Opening12_0.source
    · exact JFo_Opening12_1.source
    · exact JFo_Opening12_2.source
    · exact JFo_Opening12_3.source
  · refine ⟨![SAQ_RecordDecode.fromRecord JFo_Opening13_0.value,SAQ_RecordDecode.fromRecord JFo_Opening13_1.value,SAQ_RecordDecode.fromRecord JFo_Opening13_2.value,SAQ_RecordDecode.fromRecord JFo_Opening13_3.value],?_⟩
    intro j
    fin_cases j
    · exact JFo_Opening13_0.source
    · exact JFo_Opening13_1.source
    · exact JFo_Opening13_2.source
    · exact JFo_Opening13_3.source
  · refine ⟨![SAQ_RecordDecode.fromRecord JFo_Opening14_0.value,SAQ_RecordDecode.fromRecord JFo_Opening14_1.value,SAQ_RecordDecode.fromRecord JFo_Opening14_2.value,SAQ_RecordDecode.fromRecord JFo_Opening14_3.value],?_⟩
    intro j
    fin_cases j
    · exact JFo_Opening14_0.source
    · exact JFo_Opening14_1.source
    · exact JFo_Opening14_2.source
    · exact JFo_Opening14_3.source
  · refine ⟨![SAQ_RecordDecode.fromRecord JFo_Opening15_0.value,SAQ_RecordDecode.fromRecord JFo_Opening15_1.value,SAQ_RecordDecode.fromRecord JFo_Opening15_2.value,SAQ_RecordDecode.fromRecord JFo_Opening15_3.value],?_⟩
    intro j
    fin_cases j
    · exact JFo_Opening15_0.source
    · exact JFo_Opening15_1.source
    · exact JFo_Opening15_2.source
    · exact JFo_Opening15_3.source
  · refine ⟨![SAQ_RecordDecode.fromRecord JFo_Opening16_0.value,SAQ_RecordDecode.fromRecord JFo_Opening16_1.value,SAQ_RecordDecode.fromRecord JFo_Opening16_2.value,SAQ_RecordDecode.fromRecord JFo_Opening16_3.value],?_⟩
    intro j
    fin_cases j
    · exact JFo_Opening16_0.source
    · exact JFo_Opening16_1.source
    · exact JFo_Opening16_2.source
    · exact JFo_Opening16_3.source
  · refine ⟨![SAQ_RecordDecode.fromRecord JFo_Opening17_0.value,SAQ_RecordDecode.fromRecord JFo_Opening17_1.value,SAQ_RecordDecode.fromRecord JFo_Opening17_2.value,SAQ_RecordDecode.fromRecord JFo_Opening17_3.value],?_⟩
    intro j
    fin_cases j
    · exact JFo_Opening17_0.source
    · exact JFo_Opening17_1.source
    · exact JFo_Opening17_2.source
    · exact JFo_Opening17_3.source
  · refine ⟨![SAQ_RecordDecode.fromRecord JFo_Opening18_0.value,SAQ_RecordDecode.fromRecord JFo_Opening18_1.value,SAQ_RecordDecode.fromRecord JFo_Opening18_2.value,SAQ_RecordDecode.fromRecord JFo_Opening18_3.value],?_⟩
    intro j
    fin_cases j
    · exact JFo_Opening18_0.source
    · exact JFo_Opening18_1.source
    · exact JFo_Opening18_2.source
    · exact JFo_Opening18_3.source
  · refine ⟨![SAQ_RecordDecode.fromRecord JFo_Opening19_0.value,SAQ_RecordDecode.fromRecord JFo_Opening19_1.value,SAQ_RecordDecode.fromRecord JFo_Opening19_2.value,SAQ_RecordDecode.fromRecord JFo_Opening19_3.value],?_⟩
    intro j
    fin_cases j
    · exact JFo_Opening19_0.source
    · exact JFo_Opening19_1.source
    · exact JFo_Opening19_2.source
    · exact JFo_Opening19_3.source
  · refine ⟨![SAQ_RecordDecode.fromRecord JFo_Opening20_0.value,SAQ_RecordDecode.fromRecord JFo_Opening20_1.value,SAQ_RecordDecode.fromRecord JFo_Opening20_2.value,SAQ_RecordDecode.fromRecord JFo_Opening20_3.value],?_⟩
    intro j
    fin_cases j
    · exact JFo_Opening20_0.source
    · exact JFo_Opening20_1.source
    · exact JFo_Opening20_2.source
    · exact JFo_Opening20_3.source
  · refine ⟨![SAQ_RecordDecode.fromRecord JFo_Opening21_0.value,SAQ_RecordDecode.fromRecord JFo_Opening21_1.value,SAQ_RecordDecode.fromRecord JFo_Opening21_2.value,SAQ_RecordDecode.fromRecord JFo_Opening21_3.value],?_⟩
    intro j
    fin_cases j
    · exact JFo_Opening21_0.source
    · exact JFo_Opening21_1.source
    · exact JFo_Opening21_2.source
    · exact JFo_Opening21_3.source

/-- Partial real TX2 non-vacuity. No reader/query/finish success is assumed.
The complete native accepted wrapper pair is not asserted here. -/
theorem inhabited (seed : Port3_NativeQueryBody.Ops) :
    ∃ g : Array Tx2N_Powers.E 29#usize,
      Tx2N_Powers.powers 29#usize JFo_Prepared.value.gamma=ok g ∧
      Port3_NativePendingInstall.source true JFo_Prepared.accumulator.weights.deref=
        ok (.Ok JFo_Pending.value) ∧
      ∀ i : Fin 12, ∃ values : Fin 4 → SAQ_WideABI.E, ∀ j : Fin 4,
        (Port4C_RowStd.install (Port5Q1_QueryPorts.install (SAQ_Decoder.install seed))).op21
          (JFo_Opening.value (position i)) (slot j)=ok (values j) := by
  obtain ⟨g,run,_⟩ := JFo_Powers.source
  exact ⟨g,run,JFo_Pending.source,decoded seed⟩

#print axioms decoded
#print axioms inhabited
#print inhabited
end AspisR1.JFo_QueryFixture
end

noncomputable section
namespace AspisR1.JFo_TX2
open Aeneas Aeneas.Std Result AspisR1Stage2

/-- Transport for the TX1 half's SAME physical saved Vec. This is reader
acceptance only, conditional on the three named hash calls. No accepted2
wrapper result is asserted; query/flush/batch1/finish remain required. -/
theorem reader_on_saved (saved : alloc.vec.Vec U8)
    (same : saved.val=JFx_NativeBytes.checkpoint.val) {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H) (hash : H)
    (proofHash : D.digest hash (Array.to_slice (Array.make 1#usize [JFx_NativeBytes.proof]))=
      ok JFo_AuthBytes.proofHash)
    (publicHash : D.digest hash (Array.to_slice (Array.make 1#usize [JFx_NativeBytes.publicInput]))=
      ok JFo_AuthBytes.publicHash)
    (checksumHash : D.digest hash (Array.to_slice (Array.make 2#usize
      [Array.to_slice (Array.make 22#usize
        [85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,58#u8,82#u8,49#u8,58#u8,
         99#u8,104#u8,101#u8,99#u8,107#u8,112#u8,111#u8,105#u8,110#u8,116#u8]),
       JFq_Range.segment 0 1736 (by decide)]))=ok JFo_AuthBytes.checksum) :
    Port4A_ReaderInstall.reader true D (⟨saved.val,saved.property⟩ : Slice U8)
      JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) := by
  have bytes : (⟨saved.val,saved.property⟩ : Slice U8)=JFx_NativeBytes.checkpoint := Subtype.ext same
  rw [bytes]
  exact (JFo_ResumeNative.source D hash proofHash publicHash checksumHash).2

#print axioms reader_on_saved
#print reader_on_saved
end AspisR1.JFo_TX2
end
