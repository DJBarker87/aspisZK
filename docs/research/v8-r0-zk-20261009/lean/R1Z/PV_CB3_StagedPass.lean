import R1Z.PV_CB3_ArrayEight
import R1Z.PV_CB3_StagedWord
import R1Z.PV_CB3_SourcePass
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedPass
open Aeneas Aeneas.Std Result
/-- Exact monadic pass composition; the scalar source steps stay symbolic. -/
theorem compose (rank : Array U32 8#usize) :
    ∃ (q : Array U32 8#usize) (r : U64),
      PV_CB3_StagedSource.staged_reference.pass rank = ok (q,UScalar.cast .U32 r) ∧
      PV_CB3_SourcePass.pass rank.val = ok (q.val,r) := by
  obtain ⟨a,b,c,d,e,f,g,h,hview⟩ := PV_CB3_ArrayEight.view rank
  subst rank
  obtain ⟨qh,r1,s1⟩ := PV_CB3_SamplerWordSource.word_total h 0#u64
  obtain ⟨qg,r2,s2⟩ := PV_CB3_SamplerWordSource.word_total g r1
  obtain ⟨qf,r3,s3⟩ := PV_CB3_SamplerWordSource.word_total f r2
  obtain ⟨qe,r4,s4⟩ := PV_CB3_SamplerWordSource.word_total e r3
  obtain ⟨qd,r5,s5⟩ := PV_CB3_SamplerWordSource.word_total d r4
  obtain ⟨qc,r6,s6⟩ := PV_CB3_SamplerWordSource.word_total c r5
  obtain ⟨qb,r7,s7⟩ := PV_CB3_SamplerWordSource.word_total b r6
  obtain ⟨qa,r8,s8⟩ := PV_CB3_SamplerWordSource.word_total a r7
  refine ⟨Array.make 8#usize [qa,qb,qc,qd,qe,qf,qg,qh],r8,?_,?_⟩
  · simp [PV_CB3_StagedSource.staged_reference.pass,
      PV_CB3_StagedWord.word_eq,Array.index_usize,Array.make,lift,bind_tc_ok,
      s1,s2,s3,s4,s5,s6,s7,s8]
  · simp [PV_CB3_SourcePass.pass,Array.make,bind_tc_ok,
      s1,s2,s3,s4,s5,s6,s7,s8]

/-- The complete extracted pass Result refines the proved long-division model. -/
theorem spec (rank : Array U32 8#usize) :
    ∃ (q : Array U32 8#usize) (r : U64),
      PV_CB3_StagedSource.staged_reference.pass rank = ok (q,UScalar.cast .U32 r) ∧
      PV_CB3_SourcePass.values q.val =
        (PV_CB3_SamplerDivision.divideLE PV_CB3_SamplerWord.base PV_CB3_SamplerWord.radix
          (PV_CB3_SourcePass.values rank.val)).1 ∧
      r.val =
        (PV_CB3_SamplerDivision.divideLE PV_CB3_SamplerWord.base PV_CB3_SamplerWord.radix
          (PV_CB3_SourcePass.values rank.val)).2 := by
  obtain ⟨q,r,hs,hp⟩ := compose rank
  obtain ⟨qs,r',ht,hq,hr⟩ := PV_CB3_SourcePass.total rank.val
  have ee : (q.val,r) = (qs,r') := Result.ok.inj (hp.symm.trans ht)
  have eqs := congrArg Prod.fst ee
  have ers := congrArg Prod.snd ee
  simp only [Prod.fst,Prod.snd] at eqs ers
  subst qs
  subst r'
  exact ⟨q,r,hs,hq,hr⟩
#print axioms compose
#print axioms spec
end R1Z.PV_CB3_StagedPass
