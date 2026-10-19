import CuSavingsRhoVector

/-! Query-local all-row arithmetic composition. Every coefficient is updated
once at the old counter; the counter advances only after that full traversal.
The source caller/index enumeration and basis construction are separate bindings.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoQueryBatch
open Aeneas Aeneas.Std Result AspisR1CuRho
open CuSavingsRhoValue CuSavingsRhoPush CuSavingsRhoPushStep CuSavingsRhoState
open CuSavingsRhoInitRow CuSavingsRhoReference CuSavingsRhoVector CuSavingsResidues
open CuSavingsRhoFinishModel

def batch (power : field.QM31) (items : List (Usize × U32))
    (self : verifier.BatchedWeights) : Result verifier.BatchedWeights := do
  let out ← updates power items self
  let terms ← UScalar.add out.terms 1#usize
  .ok {out with terms := terms}

theorem batch_success (items : List (Usize × U32)) (self : verifier.BatchedWeights)
    (power : field.QM31) (hgood : Good self []) (hp : Canonical power)
    (hi : ∀ pair ∈ items,pair.1.val < self.raw.val.length)
    (hb : ∀ pair ∈ items,pair.2.val < AspisV8R17.RawReducer.P)
    (hnodup : (items.map (fun pair => pair.1.val)).Nodup)
    (hcover : ∀ i : Usize,i.val < self.raw.val.length →
      i.val ∈ items.map (fun pair => pair.1.val))
    (hcount : self.terms.val < 22) :
    ∃ out : verifier.BatchedWeights,
      batch power items self = .ok out ∧
      referenceUpdates power items (canonicalSlice self) = .ok (canonicalSlice out) ∧
      out.terms.val = self.terms.val+1 ∧
      out.raw.val.length = self.raw.val.length ∧ Good out [] := by
  obtain ⟨next,hrun,href,hterms,hlen,hg⟩ := updates_success items self [] power hgood hp hi hb
    (by intro pair _;simp only [List.not_mem_nil,not_false_eq_true]) hnodup
  have hfit : next.terms.val+(1#usize).val < 2^UScalarTy.Usize.numBits := by
    rw [hterms]
    have hlarge : 22 < 2^UScalarTy.Usize.numBits := by scalar_tac
    change self.terms.val+1 < 2^UScalarTy.Usize.numBits
    omega
  obtain ⟨terms,hadd,hval⟩ := ExtractedCurrentReducerOps.tryMk_success
    (next.terms.val+(1#usize).val) hfit
  change UScalar.add next.terms 1#usize = .ok terms at hadd
  have hone : (1#usize).val = 1 := by scalar_tac
  rw [hone] at hval
  let out := {next with terms := terms}
  refine ⟨out,?_,href,?_,hlen,?_⟩
  · simp only [batch,hrun,bind_tc_ok,hadd,out]
  · change terms.val = self.terms.val+1
    simpa only [hterms] using hval
  · intro i hi' j
    have hiv : i.val < self.raw.val.length := by simpa only [out,hlen] using hi'
    have hm := hcover i hiv
    have hmem : i.val ∈ (items.map (fun pair => pair.1.val)).reverse ++ [] := by
      simpa only [List.append_nil,List.mem_reverse] using hm
    have h := hg i hi' j
    simp only [if_pos hmem] at h
    change RhoBound (wordAt (next.raw.val[i.val]'hi') j).val
      (terms.val+if i.val ∈ [] then 1 else 0)
    simp only [List.not_mem_nil,ite_false,Nat.add_zero]
    rw [hval]
    exact h

theorem batch_finish (items : List (Usize × U32)) (self out : verifier.BatchedWeights)
    (power : field.QM31) (weights : Slice field.QM31)
    (hlen : weights.val.length = out.raw.val.length)
    (href : referenceUpdates power items (canonicalSlice self) = .ok (canonicalSlice out)) :
    referenceUpdates power items (canonicalSlice self) =
      AspisR1CuRhoSource.verifier.BatchedWeights.finish out weights := by
  rw [CuSavingsRhoSourceFinish.source_success out weights hlen]
  exact href

#print axioms batch_success
#print axioms batch_finish
end AspisR1.CuSavingsRhoQueryBatch
