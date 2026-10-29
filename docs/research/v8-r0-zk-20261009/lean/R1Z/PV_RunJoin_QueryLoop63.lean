import R1Z.PV_RunJoin_QuerySize63
import R1Z.PV_RunJoin_ByteSequence63
import R1Z.PV_RunJoin_BindSuccess63
import R1Z.ProverRw19LoopBind
import R1Z.PV_RunJoin_QueryRoom63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryLoop63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_QueryScript63 (W)
variable [ExternalTypes] [ExternalFuns]

def series (cc1 cc2 : host_commitment.Commitment) (queries : Array U32 22#usize)
    (folded : Slice W) (salts : host_commitment.PrivateSalts) : Nat → Usize → PV_RunJoin_ByteScript63.Code
  | 0,_ => .done
  | n+1,i => PV_RunJoin_ByteSequence63.append
      (PV_RunJoin_QueryScript63.script cc1 cc2 queries folded salts i)
      (series cc1 cc2 queries folded salts n (Usize.wrapping_add i 1#usize))

end R1Z.PV_RunJoin_QueryLoop63
namespace R1Z.PV_RunJoin_QueryLoop63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_QueryScript63 (W)
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem loop (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (cc1 cc2 : host_commitment.Commitment)
    (queries : Array U32 22#usize) (range : PV_RunJoin_PublishSkeleton57.QueryRange queries)
    (folded : Slice W) (salts : host_commitment.PrivateSalts)
    (n : Nat) (i : Usize) (out : alloc.vec.Vec U8)
    (rank : i.val+n=22) (room : out.length+832*n≤Usize.max) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box ops
    prover.append_query_openings_loop out cc1 cc2 queries folded salts i=
      PV_RunJoin_ByteScript63.run (series cc1 cc2 queries folded salts n i) out := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  induction n generalizing i out with
  | zero =>
    have stop : ¬ i<22#usize := by change ¬i.val<22;omega
    unfold prover.append_query_openings_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [prover.append_query_openings_loop.body,stop,if_false,bind_tc_ok,series,PV_RunJoin_ByteScript63.run]
  | succ n ih =>
    have more : i<22#usize := by change i.val<22;omega
    have nextIndex := ProverCommitPairCounter47.next_val i (by change i.val<1024;omega)
    unfold prover.append_query_openings_loop
    rw [ProverRw19LoopBind.loop_bind]
    dsimp only
    have roomParts := PV_RunJoin_QueryRoom63.split out.length Usize.max n 832 608 PV_RunJoin_QueryRoom63.widths room
    rw [PV_RunJoin_QueryFactor63.body base heap box ops cc1 cc2 queries folded salts out i more roomParts.1]
    simp only [bind_assoc_eq,bind_tc_ok,series,PV_RunJoin_ByteSequence63.run]
    apply PV_RunJoin_BindSuccess63.congr
    intro next success
    let atFin : Fin 22 := ⟨i.val,more⟩
    have index : PV_RunJoin_QueryCell63.index atFin=i := by apply UScalar.eq_of_val_eq;rfl
    have hsize := PV_RunJoin_QuerySize63.script base heap box ops cc1 cc2 queries range folded salts atFin out
    rw [index] at hsize
    have hlen := PV_RunJoin_ResultPost41.success _ _ _ hsize success
    have tailRoom : next.length+832*n≤Usize.max := roomParts.2 next.length hlen
    change prover.append_query_openings_loop next cc1 cc2 queries folded salts (Usize.wrapping_add i 1#usize)=_
    exact ih (Usize.wrapping_add i 1#usize) next (by rw [nextIndex];omega) tailRoom

#print axioms series
#print axioms loop
end R1Z.PV_RunJoin_QueryLoop63
