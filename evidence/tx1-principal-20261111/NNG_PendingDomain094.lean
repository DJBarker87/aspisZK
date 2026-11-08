import NNG_AccumulatorDomain094
import NFW_QueryEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PendingDomain094
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1
/-- Exact successful pending constructor result, with both allocation arms
preserved by its graph; no success is assumed independently of that call. -/
theorem native (env : RSL.Env) (a : LIB_VCarriers.Acc) (b : LIB_VCarriers.Weights)
 (ev : List RSL.Event) (returned : LIBC_WeightsNew.child.run a env ⟨.ret (.ok b),ev⟩) :
 LIBC_WeightsNew.model a env=ok (.Ok b) := by
 have observation := returned.2
 change RSL.Obs.mk (.ret (.ok b)) ev =
  LIB_Carriers.resultObs LIBC_WeightsNew.port [] (LIBC_WeightsNew.model a env) at observation
 cases run : LIBC_WeightsNew.model a env with
 | fail e=>rw [run] at observation;cases congrArg RSL.Obs.exit observation
 | div=>rw [run] at observation;cases congrArg RSL.Obs.exit observation
 | ok reply=>
   rw [run] at observation
   cases reply with
   | Err e=>cases congrArg RSL.Obs.exit observation
   | Ok raw=>
     have equal : b=raw := Except.ok.inj (RSL.Exit.ret.inj (congrArg RSL.Obs.exit observation))
     subst raw
     rfl
#print axioms native

/-- Actual initializer and pending outputs are the concrete states used by
NFW's query induction. The rho premise is the SAME Prepared producer fact. -/
theorem initial (env : RSL.Env) (a : LIB_VCarriers.Acc) (b : LIB_VCarriers.Weights)
 (ea eb : List RSL.Event) (p : AspisR1Stage2.verifier.Prepared)
 (newA : LIBC_AccNew.child.run () env ⟨.ret (.ok a),ea⟩)
 (newB : LIBC_WeightsNew.child.run a env ⟨.ret (.ok b),eb⟩)
 (rho : NBF_PowerStep.Canonical p.rho) :
 NFS_QueryInvariant.Domain p 0 10 (LIBC_VStateCarriers.toAcc a) b ∧
 (LIBC_VStateCarriers.toAcc a).next.val=0 := by
 obtain ⟨raw,run,same⟩ := NNG_AccumulatorDomain094.native env a ea newA
 subst a
 have fields := NNG_AccumulatorFacts094.native_fields env raw run
 have ae : raw=NFW_QueryEntry.initial := by
  cases raw with
  | mk weights rhs power next=>
    have hw : weights=NFW_QueryEntry.weights := Subtype.ext fields.2.1
    cases hw
    cases fields.2.2.1
    cases fields.2.2.2.1
    cases fields.2.2.2.2
    rfl
 have pending := native env (LIBC_VStateCarriers.fromAcc raw) b eb newB
 unfold LIBC_WeightsNew.model at pending
 rw [LIBC_VStateCarriers.to_from_acc,ae] at pending
 have size : NFW_QueryEntry.initial.weights.deref.val.length=64 := by
  change (List.replicate 64 NFW_QueryEntry.zeroQ).length=64
  exact List.length_replicate ..
 have source : Port3_NativePendingInstall.source env.reservation NFW_QueryEntry.initial.weights.deref=ok (.Ok b) := by
  rw [Port3_NativePendingInstall.reference_eq _ _ size]
  exact pending
 have bp := Port3_NativePendingInstall.accepted_fields env.reservation _ b size source
 have rawEq : b.raw=NFW_QueryEntry.pending.raw := by
  apply Subtype.ext
  rw [bp.2.1]
  simp only [NFW_QueryEntry.initial,NFW_QueryEntry.weights,NFW_QueryEntry.pending,
   NFW_QueryEntry.rowWeights,S7Kani3CallerTrace.initialRaw,List.map_replicate]
  rfl
 have be : b=NFW_QueryEntry.pending := by
  cases b with
  | mk raw terms=>
    cases rawEq
    cases bp.2.2.1
    rfl
 rw [LIBC_VStateCarriers.to_from_acc,ae,be]
 exact ⟨NFW_QueryEntry.domain p rho,rfl⟩
#print axioms initial
end AspisR1.NNG_PendingDomain094
