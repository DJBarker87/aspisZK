import LIBC_Geometry
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_GeometryReturned094
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- A returned Ok geometry has the SAME full deterministic model result;
the additional allocation-abort arm cannot manufacture a returned value. -/
theorem model (p : LIB_VCarriers.Prepared) (env : RSL.Env) (geo : LIB_VCarriers.Geo) (ev : List RSL.Event)
 (returned : LIBC_Geometry.child.run (p,0,10) env ⟨.ret (.ok geo),ev⟩) :
 LIBC_Geometry.model (p,0,10) env=ok (.Ok geo) := by
 rcases returned.2 with observation | ⟨_,stopped⟩
 · cases run : LIBC_Geometry.model (p,0,10) env with
   | fail e=>rw [run] at observation;cases congrArg RSL.Obs.exit observation
   | div=>rw [run] at observation;cases congrArg RSL.Obs.exit observation
   | ok reply=>
     rw [run] at observation
     cases reply with
     | Err e=>cases congrArg RSL.Obs.exit observation
     | Ok raw=>
       have same : geo=raw := Except.ok.inj (RSL.Exit.ret.inj (congrArg RSL.Obs.exit observation))
       subst raw
       rfl
 · cases congrArg RSL.Obs.exit stopped
#print axioms model

theorem native (p : LIB_VCarriers.Prepared) (env : RSL.Env) (geo : LIB_VCarriers.Geo) (ev : List RSL.Event)
 (returned : LIBC_Geometry.child.run (p,0,10) env ⟨.ret (.ok geo),ev⟩) :
 Port3_GeometryStage.geometry NFN_NEW_GeometryDictionary.adopted p.queries 0#usize 10#usize=ok (.Ok geo) := by
 have same := model p env geo ev returned
 have zero : LIBC_Usize.raw 0=0#usize := LIBC_Usize.from_native 0#usize (by scalar_tac)
 have ten : LIBC_Usize.raw 10=10#usize := LIBC_Usize.from_native 10#usize (by scalar_tac)
 simpa only [LIBC_Geometry.model,zero,ten] using same
#print axioms native

theorem raw (p : LIB_VCarriers.Prepared) (env : RSL.Env) (geo : LIB_VCarriers.Geo) (ev : List RSL.Event)
 (returned : LIBC_Geometry.child.run (p,0,10) env ⟨.ret (.ok geo),ev⟩) :
 NFN_NEW_GeometryRawInterface.resultMap NFN_NEW_GeometryRawInterface.answer
  (NEW_GeometryActual.verifier.QueryGeometry.for_range p.queries 0#usize 10#usize)=ok (.Ok geo) := by
 apply (Port3_QueryInstall.success_iff _ geo).mp
 rw [NFN_NEW_GeometryComplete.complete]
 exact native p env geo ev returned
#print axioms raw
end AspisR1.NNG_GeometryReturned094
