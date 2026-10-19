import CuSavingsRhoReferenceTraversal
import CuSavingsRhoBasis

/-! Source-consuming batch comparison. The old side is the entire emitted
coefficient loop; basis admission is derived from the actual emitted basis.
The optimized coefficient-loop reborrow binding and caller invariants remain
separate obligations: this theorem does not pretend that batch is that source.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoSourceBatch
open Aeneas Aeneas.Std Result AspisR1CuRho
open CuSavingsRhoInitRow CuSavingsRhoVector CuSavingsRhoValue CuSavingsRhoQueryBatch

theorem source_batch (self : verifier.BatchedWeights) (power : field.QM31)
    (node : U32) (basis : CuSavingsRhoInputs.Basis) (next : Usize)
    (hg : Good self []) (hp : Canonical power) (hn : next.val ≤ 22)
    (hl : (alloc.vec.Vec.len (canonicalSlice self)).val ≤ 256)
    (hc : self.terms.val < 22)
    (hb : AspisR1RhoBasis.basis (alloc.vec.Vec.len (canonicalSlice self)) node = .ok basis) :
    ∃ out : verifier.BatchedWeights,
      batch power (CuSavingsRhoInputs.items basis (alloc.vec.Vec.len (canonicalSlice self)) hl) self = .ok out ∧
      AspisR1RhoCoefficients.rho_old.coefficients (canonicalSlice self) power next basis =
        .ok (canonicalSlice out) ∧
      out.terms.val=self.terms.val+1 ∧ out.raw.val.length=self.raw.val.length ∧ Good out [] := by
  let length := alloc.vec.Vec.len (canonicalSlice self)
  have hlen : length.val=self.raw.val.length := by
    simp only [length,alloc.vec.Vec.len,Slice.len_val,Slice.length,canonicalSlice,List.length_map]
  have ha := CuSavingsRhoBasis.input_admitted length node basis power hl hp hb
  have hadmit : CuSavingsRhoBatches.Admitted
      {power:=power,items:=CuSavingsRhoInputs.items basis length hl} self.raw.val.length := by
    rw [← hlen]
    exact ha
  obtain ⟨out,hrun,href,hcount,hlength,hgood⟩ := batch_success
    (CuSavingsRhoInputs.items basis length hl) self power hg
    hadmit.1 hadmit.2.1 hadmit.2.2.1 hadmit.2.2.2.1 hadmit.2.2.2.2 hc
  refine ⟨out,hrun,?_,hcount,hlength,hgood⟩
  rw [CuSavingsRhoReferenceTraversal.source_eq (canonicalSlice self) power next basis hn hl]
  exact href

#print axioms source_batch
end AspisR1.CuSavingsRhoSourceBatch
