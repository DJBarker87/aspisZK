import PV_LIB_A_F170Tail15
import PV_LIB_SPEC_LaneAJoins18
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F170Result16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_A_SourceSequence13
open PV_LIB_A_SequenceFrontier13 (prepend)

def kind : Data := match PV_THR2_F170.node59 with
  | .leaf (.aggregateMove _ _ k _) => k | _ => .null

def stored (s : Store Data) (a : Nat) (v : Data) : Store Data :=
  let s := write (write (write s ⟨a,17,[]⟩ none) ⟨a,16,[]⟩ none) ⟨a,15,[]⟩ none
  let s := write (write s ⟨a,14,[]⟩ none) ⟨a,0,[]⟩ (some (PV_THR2_KeyValues.pack kind [v]))
  write (write (write (write (write s ⟨a,14,[]⟩ none) ⟨a,3,[]⟩ none)
    ⟨a,18,[]⟩ none) ⟨a,2,[]⟩ none) ⟨a,1,[]⟩ none

theorem computed (p : Parameters) (s : Store Data) (a : Nat) (v : Data)
    (parents : List Frame) (w : OWNER) (value : s.cells ⟨a,14,[]⟩ = some v) :
    steps (runtime p).carrier a w PV_LIB_A_F170Tail15.seq s = 9 ∧
    result (runtime p).carrier a parents [] (PV_THR2_F170.live.body.drop 49) w
      PV_LIB_A_F170Tail15.seq s =
      .running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 49},parents,stored s a v⟩ := by
  have missing : (runtime p).carrier.aggregate kind [v] = none := rfl
  have packing : (PV_THR2_AggregateCompletion.carrier (runtime p).carrier).aggregate kind [v] =
      some (PV_THR2_KeyValues.pack kind [v]) := rfl
  simp only [kind,PV_THR2_F170.node59] at missing packing
  simp [PV_LIB_A_F170Tail15.seq,prepend,PV_THR2_F170.node56,PV_THR2_F170.node57,
    PV_THR2_F170.node58,PV_THR2_F170.node59,PV_THR2_F170.node60,PV_THR2_F170.node61,
    PV_THR2_F170.node62,PV_THR2_F170.node63,PV_THR2_F170.node64,
    steps,result,bound,PV_THR2_IntrinsicFrameChain.bound,PV_STX2_Store.bind,
    evaluate,operands,operand,PV_STX2_Store.read,locate,writeAddress,write,
    value,missing,packing,stored,kind]

#print axioms computed
end PV_LIB_A_F170Result16
