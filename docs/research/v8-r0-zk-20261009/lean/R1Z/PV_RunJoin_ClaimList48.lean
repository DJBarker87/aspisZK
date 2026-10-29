import R1Z.PV_RunJoin_ClaimThread48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimList48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ClaimThread48 (Column Point)
variable [ExternalTypes] [ExternalFuns]

def cell (point : Point) (out : alloc.vec.Vec U8) (column : Column) := do
  let value ← aspis_core.r0.encoder.eval_message
    aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField column point
  let wire ← aspis_core.field.wide_exact.WideExact.to_le_bytes value
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out (Array.to_slice wire)

def run (point : Point) : List Column → alloc.vec.Vec U8 → Result (alloc.vec.Vec U8)
  | [],out => ok out
  | column::tail,out => do
    let next ← cell point out column
    run point tail next

theorem read {A : Type} (s : Slice A) (i : Usize) (h : i.val<s.val.length) :
    Slice.index_usize s i=ok (s.val[i.val]'h) := by
  simp only [Slice.index_usize,Slice.getElem?_Usize_eq,List.getElem?_eq_getElem h]

theorem complete (messages : Slice Column) (point : Point) (n : Nat)
    (out : alloc.vec.Vec U8) (lane : Usize) (small : messages.length≤14336)
    (rank : lane.val+n=messages.length) :
    PV_RunJoin_ClaimThread48.phase messages point n out lane=
      run point (messages.val.drop lane.val) out := by
  have len : messages.val.length=messages.length := rfl
  induction n generalizing out lane with
  | zero =>
    rw [List.drop_eq_nil_of_le (show messages.val.length≤lane.val by omega)]
    rfl
  | succ n ih =>
    have hi : lane.val<messages.val.length := by omega
    rw [List.drop_eq_getElem_cons hi]
    simp only [PV_RunJoin_ClaimThread48.phase,PV_RunJoin_ClaimThread48.step,read messages lane hi,
      bind_tc_ok,run,cell,bind_assoc]
    apply congrArg (Aeneas.Std.bind _)
    funext value
    apply congrArg (Aeneas.Std.bind _)
    funext wire
    apply congrArg (Aeneas.Std.bind _)
    funext next
    rw [ih next _ (by rw [PV_RunJoin_MergeLoop35.increment lane (by omega)];omega)]
    rw [PV_RunJoin_MergeLoop35.increment lane (by omega)]
#print axioms read
#print axioms complete
end R1Z.PV_RunJoin_ClaimList48
