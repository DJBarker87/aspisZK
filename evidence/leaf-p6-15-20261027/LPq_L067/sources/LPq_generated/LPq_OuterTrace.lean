import LPq_ArrayPorts
set_option autoImplicit false
namespace AspisR1.LPq_OuterTrace
open Aeneas Aeneas.Std Result ControlFlow LPi_FieldValues LPm_RawPort XRo_Join_Carriers
open AspisR1CurrentPreparedClaim
abbrev Range := LPm_PointLoop.Range
abbrev Seven := LPq_WeightedStep.Seven

/-- Source-local outer observations. Each nested Dot trace uses the SAME
semantic carrier, selected bytes and coefficient array. The final component
is the previously paired seven-step native weighting, not a body equality. -/
inductive Trace {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array Concrete.E 29#usize) (k : Seven) : Range → Seven → NE → Prop where
  | done (iter iter' : Range) (parts : Seven) (out : NE)
      (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (none,iter'))
      (sum : LPq_Weighted.run k parts 7 0#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out) :
      Trace sem y1 g k iter parts out
  | step {iter iter' : Range} {parts : Seven} {out : NE}
      (point i : Usize) (value : NE) (xs : List (NE×NQ))
      (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some point,iter'))
      (dot : LPm_PointLoop.Trace sem y1 g point
        {start:=0#usize,«end»:=29#usize} LPm_PublicTwentyNine.zero xs value)
      (increment : (point+1#usize : Result Usize)=ok i) (within : i.val<7)
      (tail : Trace sem y1 g k iter' (parts.set i value) out) :
      Trace sem y1 g k iter parts out

theorem point_source {H : Type} (inst : aspis_core.Digest32 H)
    {sem : r1_semantic.Verified H} {y1 : Slice U8} {g : Array Concrete.E 29#usize}
    {point : Usize} {xs : List (NE×NQ)} {value : NE}
    (tr : LPm_PointLoop.Trace sem y1 g point
      {start:=0#usize,«end»:=29#usize} LPm_PublicTwentyNine.zero xs value) :
    verifier.prepared_claim_dot LPm_PointLoop.ops inst sem y1 g point=ok (.Ok (LPq_Powers.claim value)) := by
  change verifier.prepared_claim_dot_loop LPm_PointLoop.ops inst
    {start:=0#usize,«end»:=29#usize} sem y1 g point
    (statePort LPm_PublicTwentyNine.zero)=_
  exact LPm_PointLoop.source inst tr

/-- Whole outer Result follows from linked local calls. There is no supplied
whole prepared_claim Result, independent part inventory or public sum. -/
theorem source {H : Type} (inst : aspis_core.Digest32 H)
    {sem : r1_semantic.Verified H} {y1 : Slice U8} {g : Array Concrete.E 29#usize}
    {k parts : Seven} {iter : Range} {out : NE}
    (hk : LPq_WeightedStep.canonical k) (hp : LPq_WeightedStep.canonical parts)
    (tr : Trace sem y1 g k iter parts out) :
    verifier.prepared_claim_loop LPm_PointLoop.ops inst iter sem y1 g
      (arr LPq_Powers.claim k) (arr LPq_Powers.claim parts)=ok (.Ok (LPq_Powers.claim out)) := by
  induction tr with
  | done iter iter' parts out next sum =>
    obtain ⟨actual,en,_,model⟩ := LPq_Weighted.source k parts hk hp
    have same : actual=out := Result.ok.inj (en.symm.trans sum)
    rw [same] at model
    have body : verifier.prepared_claim_loop.body LPm_PointLoop.ops inst sem y1 g
        (arr LPq_Powers.claim k) iter (arr LPq_Powers.claim parts)=
        ok (ControlFlow.done (.Ok (LPq_Powers.claim out))) := by
      rw [verifier.prepared_claim_loop.body,next,bind_tc_ok]
      rw [model,bind_tc_ok]
    change Aeneas.Std.loop _ _=_
    rw [Aeneas.Std.loop.eq_def]
    dsimp only
    rw [body]
  | @step iter iter' parts out point i value xs next dot increment within tail ih =>
    have model := point_source inst dot
    have write := LPq_ArrayPorts.mapped LPq_Powers.claim parts i value within
    have hp' := LPq_ArrayPorts.canonical_set parts i value hp (LPq_OutputDomains.point dot)
    have body : verifier.prepared_claim_loop.body LPm_PointLoop.ops inst sem y1 g
        (arr LPq_Powers.claim k) iter (arr LPq_Powers.claim parts)=
        ok (ControlFlow.cont (iter',arr LPq_Powers.claim (parts.set i value))) := by
      rw [verifier.prepared_claim_loop.body,next,bind_tc_ok]
      simp only [model,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch,increment,write]
    change Aeneas.Std.loop _ _=_
    rw [Aeneas.Std.loop.eq_def]
    dsimp only
    rw [body]
    exact ih hp'

#print axioms point_source
#print axioms source
end AspisR1.LPq_OuterTrace
