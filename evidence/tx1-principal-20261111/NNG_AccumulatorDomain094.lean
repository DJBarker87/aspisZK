import NNG_AccumulatorFacts094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_AccumulatorDomain094
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1
/-- Every actual returned Ok arm has the SAME native constructor result. -/
theorem native (env : RSL.Env) (a : LIB_VCarriers.Acc) (ev : List RSL.Event)
 (returned : LIBC_AccNew.child.run () env ⟨.ret (.ok a),ev⟩) :
 ∃ raw,LIBC_AccNew.model env=ok (.Ok raw) ∧ a=LIBC_VStateCarriers.fromAcc raw := by
 have observation := returned.2
 change RSL.Obs.mk (.ret (.ok a)) ev =
  LIB_Carriers.resultObs LIBC_AccNew.port [] (LIBC_AccNew.model env) at observation
 cases run : LIBC_AccNew.model env with
 | fail e => rw [run] at observation;cases congrArg RSL.Obs.exit observation
 | div => rw [run] at observation;cases congrArg RSL.Obs.exit observation
 | ok reply =>
   rw [run] at observation
   cases reply with
   | Err e => cases congrArg RSL.Obs.exit observation
   | Ok raw =>
     have values := RSL.Exit.ret.inj (congrArg RSL.Obs.exit observation)
     exact ⟨raw,rfl,Except.ok.inj values⟩
#print axioms native

/-- The constructor itself discharges the pending-weight child's64-cell and
canonicality clauses. No reservation-success hypothesis is added. -/
theorem weights_domain (env : RSL.Env) (a : LIB_VCarriers.Acc) (ev : List RSL.Event)
 (returned : LIBC_AccNew.child.run () env ⟨.ret (.ok a),ev⟩) :
 LIBC_WeightsNew.Domain a := by
 obtain ⟨raw,run,same⟩ := native env a ev returned
 subst a
 have fields := NNG_AccumulatorFacts094.native_fields env raw run
 constructor
 · change (raw.weights.val.map LIBC_VStateCarriers.fromQ).length=64
   rw [List.length_map,fields.2.1,List.length_replicate]
 · intro q member
   change q∈raw.weights.val.map LIBC_VStateCarriers.fromQ at member
   obtain ⟨value,original,rfl⟩ := List.mem_map.mp member
   rw [fields.2.1] at original
   have same : value=Port2_Initial.zeroK := (List.mem_replicate.mp original).2
   subst value
   rw [LIBC_VStateCarriers.to_from_q]
   exact ⟨by decide,by decide,by decide,by decide⟩
#print axioms weights_domain
end AspisR1.NNG_AccumulatorDomain094
