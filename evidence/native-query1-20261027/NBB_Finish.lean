import Port3_FlushInstall
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBB_Finish
open AspisR1.Port3_FlushInstall
/-- Every actual 64-weight destination is fully materialized, on arbitrary raw
U64 rows. No phase or canonicality precondition is needed by finish. -/
theorem source (b : BW) (old : Slice K)
 (raw64 : b.raw.val.length=64) (old64 : old.val.length=64) :
 ∃ out : Slice K, flush b old=ok out ∧ out.val.length=64 ∧
 out.val=((b.raw.val.take 64).map (fun row => fromMutable
  (S8Kani2FinishReferenceJoin.toFinish (S8OwnedP6Finish.modelValue row)))) ∧
 (∀ q∈out.val, Canonical q) := by
 have lengths : old.val.length≤b.raw.val.length := by omega
 let out := fromSlice
  ⟨(S8JoinFinishExact.output b.raw (toWeights old)).val.map S8Kani2FinishReferenceJoin.toFinish,
   by simpa using (S8JoinFinishExact.output b.raw (toWeights old)).property⟩
 have run : flush b old=ok out := flush_exact b old lengths
 obtain ⟨contents,len⟩ := accepted_contents b old out lengths run
 exact ⟨out,run,len.trans old64,by simpa only [old64] using contents,
  accepted_canonical b old out lengths run⟩

theorem unique (b : BW) (old x y : Slice K)
 (hx : flush b old=ok x) (hy : flush b old=ok y) : x=y :=
 Result.ok.inj (hx.symm.trans hy)
#print axioms source
#print axioms unique
end NBB_Finish
