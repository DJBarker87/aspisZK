import FIw_PackValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_PackSource
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (K Canon decode)

theorem generated_eq (values : Slice NQ) : field.qm31_pack_base4 values=(do
    massert (Slice.len values≤4#usize)
    let copied ← ExtractedMaskQmPackBase4InitCopy.copyPrefixWith field.QM31.ZERO
      field.QM31.Insts.CoreMarkerCopy values
    FIw_PackArithmetic.afterArray copied) := by
  simp only [field.qm31_pack_base4,ExtractedMaskQmPackBase4InitCopy.copyPrefixWith,
    FIw_PackArithmetic.afterArray,bind_assoc_eq,bind_tc_ok]
  congr 1
  funext unit
  congr 1
  funext pair
  cases pair
  rfl

theorem value (values : Slice NQ) (out : NQ) (len : values.length=4)
    (hc : ∀ x∈values.val,Canon x) (run : field.qm31_pack_base4 values=ok out) :
    ∃ copied : Array NQ 4#usize,copied.val=values.val ∧
      Canon out ∧ decode out=ExtractedMaskQmPackBase4Arithmetic.mathematicalPack
        (fun j=>qm (FIw_ArrayValue.cells copied j)) := by
  obtain ⟨copied,copyRun,same⟩ := ExtractedMaskQmPackBase4InitCopy.copyPrefixWith_eq_source
    field.QM31.ZERO field.QM31.Insts.CoreMarkerCopy values len
  have assertion : massert (Slice.len values≤4#usize)=ok () := by
    apply (massert_ok _).2
    have h : (Slice.len values).val=4 := len
    scalar_tac
  rw [generated_eq,assertion,bind_tc_ok,copyRun,bind_tc_ok] at run
  exact ⟨copied,same,FIw_PackValue.value copied out (by rw [same];exact hc) run⟩
#print axioms generated_eq
#print axioms value
end AspisR1.FIw_PackSource
end
