import R1Z.PV_RunJoin_NodePayloadModel60
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NodeSequence60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PublishSkeleton54
open PV_RunJoin_NodePayloadModel60 (Payload)
abbrev Input := Payload × Usize

def run : List Input → alloc.vec.Vec U8 → Payload
  | [],out => ok (.Ok out)
  | s::ss,out => do
    let status ← PV_RunJoin_NodePayloadModel60.run out s.1 s.2
    match status with
    | .Err e => ok (.Err e)
    | .Ok next => run ss next

def models (slots : List Input) := slots.map (fun s => PV_RunJoin_NodePayloadModel60.model s.1 s.2.val)
def capacities (slots : List Input) := (slots.map (fun s => s.2.val)).sum

theorem singleton (slot : Input) (out : alloc.vec.Vec U8) :
    run [slot] out=PV_RunJoin_NodePayloadModel60.run out slot.1 slot.2 := by
  unfold run
  cases h : PV_RunJoin_NodePayloadModel60.run out slot.1 slot.2 with
  | fail e => rfl
  | div => rfl
  | ok status => cases status <;> rfl
#print axioms singleton

theorem complete (slots : List Input) (out : alloc.vec.Vec U8)
    (room : out.length+2*capacities slots≤Usize.max) :
    resultBytes (run slots out)=exceptBytes (ProverCommitPublish43.slots (models slots) (bytes out.val)) := by
  induction slots generalizing out with
  | nil => rfl
  | cons s ss ih =>
    rcases s with ⟨payload,cap⟩
    change out.length+2*(cap.val+capacities ss)≤Usize.max at room
    have room1 : out.length+2*cap.val≤Usize.max := by omega
    have equivalent := PV_RunJoin_NodePayloadModel60.complete out payload cap room1
    cases hr : PV_RunJoin_NodePayloadModel60.run out payload cap with
    | fail e =>
      cases hm : ProverCommitPublish43.appendSlot (bytes out.val) (PV_RunJoin_NodePayloadModel60.model payload cap.val) with
      | error e => simp only [run,hr,bind_tc_fail,models,List.map_cons,ProverCommitPublish43.slots,hm,Bind.bind,Std.bind,Except.bind,resultBytes,exceptBytes]
      | ok b => rw [hr,hm] at equivalent;cases equivalent
    | div =>
      cases hm : ProverCommitPublish43.appendSlot (bytes out.val) (PV_RunJoin_NodePayloadModel60.model payload cap.val) with
      | error e => simp only [run,hr,bind_tc_div,models,List.map_cons,ProverCommitPublish43.slots,hm,Bind.bind,Std.bind,Except.bind,resultBytes,exceptBytes]
      | ok b => rw [hr,hm] at equivalent;cases equivalent
    | ok status =>
      cases status with
      | Err e =>
        cases hm : ProverCommitPublish43.appendSlot (bytes out.val) (PV_RunJoin_NodePayloadModel60.model payload cap.val) with
        | error e => simp only [run,hr,bind_tc_ok,models,List.map_cons,ProverCommitPublish43.slots,hm,Bind.bind,Std.bind,Except.bind,resultBytes,exceptBytes]
        | ok b => rw [hr,hm] at equivalent;cases equivalent
      | Ok next =>
        cases hm : ProverCommitPublish43.appendSlot (bytes out.val) (PV_RunJoin_NodePayloadModel60.model payload cap.val) with
        | error e => rw [hr,hm] at equivalent;cases equivalent
        | ok b =>
          rw [hr,hm] at equivalent
          have bytesEq : bytes next.val=b := Option.some.inj equivalent
          have hlen := ProverCommitPublish43.slot_length (bytes out.val)
            (PV_RunJoin_NodePayloadModel60.model payload cap.val) b hm
          have nextLen : next.length=out.length+cap.val := by
            rw [←bytesEq] at hlen
            simpa only [bytes,List.length_map,PV_RunJoin_NodePayloadModel60.model] using hlen
          have nextRoom : next.length+2*capacities ss≤Usize.max := by
            change out.length+2*(cap.val+capacities ss)≤Usize.max at room
            rw [nextLen]
            omega
          have tail := ih next nextRoom
          simpa only [run,hr,bind_tc_ok,models,List.map_cons,ProverCommitPublish43.slots,
            hm,Bind.bind,Std.bind,Except.bind,←bytesEq] using tail

#print axioms complete
end R1Z.PV_RunJoin_NodeSequence60
