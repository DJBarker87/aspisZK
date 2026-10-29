import R1Z.PV_RunJoin_NodeTail41
import R1Z.PV_RunJoin_PublishSkeleton54
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NodeTailModel60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PublishSkeleton54

theorem complete (out nodes : alloc.vec.Vec U8) (cap : Usize)
    (room : out.length+2*cap.val≤Usize.max) :
    resultBytes (do let next ← PV_RunJoin_NodeTail41.finish out nodes cap;ok (.Ok next))=
      exceptBytes (ProverCommitPublish43.appendSlot (bytes out.val) ⟨.ok (bytes nodes.val),cap.val⟩) := by
  change out.val.length+2*cap.val≤Usize.max at room
  by_cases fits : nodes.val.length≤cap.val
  · obtain ⟨next,hn,hv⟩ := PV_RunJoin_NodeTail41.accepts out nodes cap fits (by omega)
    rw [hn]
    simp only [bind_tc_ok,resultBytes,ProverCommitPublish43.appendSlot,
      Bind.bind,Except.bind,bytes,List.length_map,show ¬nodes.val.length>cap.val from (by exact Nat.not_lt.mpr fits),
      if_false,exceptBytes]
    apply congrArg some
    rw [hv,List.map_append,List.map_append,List.map_replicate]
    rfl
  · have hnot : ¬alloc.vec.Vec.len nodes≤cap := by change ¬nodes.val.length≤cap.val;exact fits
    simp only [PV_RunJoin_NodeTail41.finish,massert,hnot,if_false,bind_tc_fail,
      resultBytes,ProverCommitPublish43.appendSlot,Bind.bind,Except.bind,bytes,List.length_map,
      show nodes.val.length>cap.val from (by omega),if_true,exceptBytes]

#print axioms complete
end R1Z.PV_RunJoin_NodeTailModel60
