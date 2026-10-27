import LPq_OuterConstruct
set_option autoImplicit false
namespace AspisR1.LPq_PreparedTrace
open Aeneas Aeneas.Std Result LPi_FieldValues LPm_RawPort XRo_Join_Carriers
open AspisR1CurrentPreparedClaim
abbrev Seven := LPq_WeightedStep.Seven
abbrev zero := FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO

def initial (inactive : NE) : Seven := (Array.repeat 7#usize zero).set 0#usize inactive

theorem zero_claim : LPq_Powers.claim zero=aspis_core.field.WideExact.ZERO := by
  rw [LPq_Powers.claim,LPq_Weighted.zero_wide,XRy_ClaimSum.zero_claim]

theorem initial_canonical (inactive : NE) (hi : canonE inactive) :
    LPq_WeightedStep.canonical (initial inactive) := by
  apply LPq_ArrayPorts.canonical_set _ _ _ _ hi
  intro z hz
  have same : z=zero := (List.mem_replicate.mp hz).2
  rw [same]
  exact LPq_Weighted.zero_canonical

/-- Whole-body carrier trace: a local powers call, the source's actual initial
parts carrier and six linked point/store transitions ending in native weighting.
No whole-body equation or independently supplied final parts occurs here. -/
inductive Trace {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array Concrete.E 29#usize) (inactive kappa out : NE) : Prop where
  | mk (k : Seven) (powers : FIo_Native.weights.powers 7#usize kappa=ok k)
      (outer : LPq_OuterTrace.Trace sem y1 g k
        {start:=0#usize,«end»:=6#usize} (initial inactive) out) :
      Trace sem y1 g inactive kappa out

theorem construct {H : Type} (sem : r1_semantic.Verified H)
    (hs : LPq_ReadPorts.SemCanonical sem) (y1 : Slice U8) (hy : LPq_SixPoints.SelectedFields y1)
    (g : Array Concrete.E 29#usize) (hg : LPq_ReadPorts.WeightsCanonical g)
    (inactive kappa : NE) (hi : canonE inactive) (hk : canonE kappa) :
    ∃ out, Trace sem y1 g inactive kappa out ∧ canonE out := by
  obtain ⟨k,call,_⟩ := LPq_Powers.source 7#usize kappa hk
  have kc := LPq_OutputDomains.powers kappa hk k call
  obtain ⟨out,outer,co⟩ := LPq_OuterConstruct.loop sem y1 g k kc
    (fun p hp => LPq_SixPoints.domain sem hs y1 hy g hg p hp)
    6 {start:=0#usize,«end»:=6#usize} (initial inactive) (initial_canonical inactive hi)
    rfl (by decide) (by decide)
  exact ⟨out,⟨k,call,outer⟩,co⟩

/-- Full concrete cohort Result from ONE native local carrier trace. Local
powers uniqueness identifies the actual k, not a separately chosen array. -/
theorem source {H : Type} (inst : aspis_core.Digest32 H)
    {sem : r1_semantic.Verified H} {y1 : Slice U8} {g : Array Concrete.E 29#usize}
    {inactive kappa out : NE} (hi : canonE inactive) (hk : canonE kappa)
    (tr : Trace sem y1 g inactive kappa out) :
    AspisR1CurrentPreparedClaim.verifier.prepared_claim LPm_PointLoop.ops inst sem y1 (LPq_Powers.claim inactive) g
      (LPq_Powers.claim kappa)=ok (.Ok (LPq_Powers.claim out)) := by
  rcases tr with ⟨k,powers,outerTrace⟩
  obtain ⟨actual,native,model⟩ := LPq_Powers.source 7#usize kappa hk
  have same : actual=k := Result.ok.inj (native.symm.trans powers)
  rw [same] at model
  have outer := LPq_OuterTrace.source inst (LPq_OutputDomains.powers kappa hk k powers)
    (initial_canonical inactive hi) outerTrace
  have init := LPq_ArrayPorts.mapped LPq_Powers.claim (Array.repeat 7#usize zero)
    0#usize inactive (by decide)
  rw [XRy_ArrayMap.repeated,zero_claim] at init
  unfold AspisR1CurrentPreparedClaim.verifier.prepared_claim
  change (do
    let k ← ClaimPowers.powers 7#usize (LPq_Powers.claim kappa)
    let parts ← Array.update (Array.repeat 7#usize aspis_core.field.WideExact.ZERO) 0#usize (LPq_Powers.claim inactive)
    verifier.prepared_claim_loop LPm_PointLoop.ops inst
      {start:=0#usize,«end»:=6#usize} sem y1 g k parts)=_
  rw [model,bind_tc_ok,init,bind_tc_ok]
  exact outer

#print axioms zero_claim
#print axioms initial_canonical
#print axioms construct
#print axioms source
end AspisR1.LPq_PreparedTrace
