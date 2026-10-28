import RPv_FIw_PackSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_PackTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (K Canon decode)

theorem arithmetic (a : Array NQ 4#usize) (hc : ∀ x∈a.val,Canon x) :
    ∃ out,FIw_PackArithmetic.afterArray a=ok out ∧ Canon out ∧
      decode out=ExtractedMaskQmPackBase4Arithmetic.mathematicalPack
        (fun j=>qm (FIw_ArrayValue.cells a j)) := by
  let pa := FIw_PackArithmetic.array a
  let s := Array.to_slice pa
  have len : s.length=4 := pa.property
  have eq := ExtractedMaskQmPackBase4Whole.after_eq_run pa s rfl len
  have inputs : ExtractedMaskQmPackBase4Whole.inputAt s len=
      (fun j=>qm (FIw_ArrayValue.cells a j)) := by
    funext j
    simp only [ExtractedMaskQmPackBase4Whole.inputAt,s,pa,FIw_PackArithmetic.array,
      FIw_ArrayValue.cells,Array.to_slice,List.getElem_map]
  have can : ∀ j : Fin 4,ExtractedMaskQM31Exact.CurrentCanonicalQM
      (ExtractedMaskQmPackBase4Whole.inputAt s len j) := by
    intro j
    rw [inputs]
    change Canon (FIw_ArrayValue.cells a j)
    exact hc _ (List.getElem_mem _)
  obtain ⟨z,hz,hcanon,hvalue⟩ := ExtractedMaskQmPackBase4Fragments.run_success
    (ExtractedMaskQmPackBase4Whole.inputAt s len) can
  have same := FIw_PackArithmetic.mapped a
  change FIv_Map.map qm (FIw_PackArithmetic.afterArray a)=
    ExtractedMaskQmPackBase4Whole.afterArray pa at same
  rw [eq,hz] at same
  cases run : FIw_PackArithmetic.afterArray a with
  | fail e => rw [run] at same;cases same
  | div => rw [run] at same;cases same
  | ok out => exact ⟨out,rfl,FIw_PackValue.value a out hc run⟩

theorem source (values : Slice NQ) (len : values.length=4)
    (hc : ∀ x∈values.val,Canon x) :
    ∃ out,field.qm31_pack_base4 values=ok out ∧ Canon out := by
  obtain ⟨copied,copyRun,same⟩ := ExtractedMaskQmPackBase4InitCopy.copyPrefixWith_eq_source
    field.QM31.ZERO field.QM31.Insts.CoreMarkerCopy values len
  obtain ⟨out,after,hout,_⟩ := arithmetic copied (by rw [same];exact hc)
  have assertion : massert (Slice.len values≤4#usize)=ok () := by
    apply (massert_ok _).2
    have h : (Slice.len values).val=4 := len
    scalar_tac
  refine ⟨out,?_,hout⟩
  rw [FIw_PackSource.generated_eq,assertion,bind_tc_ok,copyRun,bind_tc_ok,after]
#print axioms arithmetic
#print axioms source
end AspisR1.FIw_PackTotal
end
