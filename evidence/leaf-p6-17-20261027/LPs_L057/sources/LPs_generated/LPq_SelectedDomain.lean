import LPq_BytesTotal
import LPq_PreparedClaim
set_option autoImplicit false
namespace AspisR1.LPq_SelectedDomain
open Aeneas Aeneas.Std Result LPi_FieldValues

def selected (y1 : Slice U8) (l : Usize) : Result (Slice U8) :=
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) y1
    {start:=Usize.wrapping_mul l 32#usize,
     «end»:=Usize.wrapping_mul (Usize.wrapping_add l 1#usize) 32#usize}

/-- Only the selected input bytes and word bounds, with the actual native slice
operation. No decoded field output or field-success observation is a premise. -/
def ByteDomain (y1 : Slice U8) : Prop := ∀ l : Usize, l.val<29 → ∃ b : Slice U8,
  selected y1 l=ok b ∧ b.val.length=32 ∧
    (∀ j, j<8 → (LPq_BytesTotal.word b j).val<2147483647)

theorem selected_fields (y1 : Slice U8) (hy : ByteDomain y1) : LPq_SixPoints.SelectedFields y1 := by
  intro l hl
  obtain ⟨b,slice,len,words⟩ := hy l hl
  obtain ⟨out,decode,co⟩ := LPq_BytesTotal.source b len words
  refine ⟨out,co,?_⟩
  change (do
    let b ← selected y1 l
    let o ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes b
    core.option.Option.unwrap o)=_
  rw [slice,bind_tc_ok,decode,bind_tc_ok]
  rfl

theorem native_result {H : Type} (sem : AspisR1CurrentPreparedClaim.r1_semantic.Verified H)
    (hs : LPq_ReadPorts.SemCanonical sem) (y1 : Slice U8) (hy : ByteDomain y1)
    (g : Array AspisR1CurrentPreparedClaim.Concrete.E 29#usize) (hg : LPq_ReadPorts.WeightsCanonical g)
    (inactive kappa : NE) (hi : canonE inactive) (hk : canonE kappa) :
    ∃ out, LPq_PreparedTrace.Trace sem y1 g inactive kappa out ∧ canonE out ∧
      LPq_PreparedClaim.program sem y1 g inactive kappa = fun _ => ok (.Ok (LPq_Powers.claim out)) :=
  LPq_PreparedClaim.native_result sem hs y1 (selected_fields y1 hy) g hg inactive kappa hi hk

#print axioms selected_fields
#print axioms native_result
end AspisR1.LPq_SelectedDomain
