import R1Z.PV_Src_PortNoopInternal
set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalMeaning
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_Src_PortTraceRounds
variable {K : Type} [Field K] [CharP K 2147483647]

def model (xs : List (Usize × U32)) (v : Fin 16 → K) : Fin 16 → K :=
  xs.foldl (fun st p => R0P.poseidonInternalRound st (liftU p.2)) v

theorem meaning (xs : List (Usize × U32)) (s input : State) (trace : Unit) (round : U8)
    (out : Output Unit)
    (ho : PV_Src_PortInternalRounds.steps PV_Src_PortNoop.callback xs s trace round input = ok out) :
    liftA (K := K) out.1 = model xs (liftA s) := by
  induction xs generalizing s input trace round with
  | nil =>
    change ok (s,trace,round,input) = ok out at ho
    rw [← Result.ok.inj ho]
    rfl
  | cons p xs ih =>
    obtain ⟨state1,hstate,hmeaning⟩ := internal_round_lift (K := K) s p.2
      R0PoseidonCopy.INTERNAL_SHIFTS PV_Src_PortInternalCopy.shifts_bound PV_Src_PortInternalCopy.shifts_model
    simp only [PV_Src_PortInternalRounds.steps,hstate,bind_tc_ok,PV_Src_PortNoop.call] at ho
    have h := ih state1 state1 trace (U8.wrapping_add round 1#u8) ho
    rw [h]
    change model xs (liftA state1) = model xs (R0P.poseidonInternalRound (liftA s) (liftU p.2))
    rw [show liftA (K := K) state1 = _ from funext hmeaning]

#print axioms meaning
end R1Z.PV_Src_PortInternalMeaning
