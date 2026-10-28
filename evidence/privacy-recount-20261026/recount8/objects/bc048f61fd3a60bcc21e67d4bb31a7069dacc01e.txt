import R1Z.PV_RunJoin_PolyCell38
import R1Z.PV_RunJoin_ByteAppend38
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimStep41
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_PolyCell38
variable [ExternalTypes]

theorem stop (ops : ExternalFuns) (p : Array Q 29#usize)
    (bytes : alloc.vec.Vec U8) (i : Usize) (hi : ¬i.val<29) :
    @host_semantic.append_claim_bytes_loop.body _ (ProverRwP6BodyCandidate.selected ops)
      p bytes i = .ok (.done bytes) := by
  simp only [host_semantic.append_claim_bytes_loop.body,show ¬i<29#usize from hi,↓reduceIte]

theorem step (ops : ExternalFuns) (p : Nat → Q)
    (bytes : alloc.vec.Vec U8) (i : Usize) (hi : i.val<29)
    (room : bytes.length+32≤Usize.max) :
    ∃ next, @host_semantic.append_claim_bytes_loop.body _ (ProverRwP6BodyCandidate.selected ops)
      (ProverCommitArray49.array 29#usize p) bytes i =
        .ok (.cont (next,Usize.wrapping_add i 1#usize)) ∧
      next.val = bytes.val ++ cell (p i.val) := by
  have hroom : bytes.length + (Array.to_slice
      (PV_RunJoin_FlatBytes35.wire (wide (p i.val)))).length ≤ Usize.max := by
    change bytes.length + (cell (p i.val)).length ≤ Usize.max
    rw [PV_RunJoin_PolyCell38.length]
    exact room
  obtain ⟨next,hnext,hval⟩ := PV_RunJoin_ByteAppend38.append bytes
    (Array.to_slice (PV_RunJoin_FlatBytes35.wire (wide (p i.val)))) hroom
  refine ⟨next,?_,hval⟩
  unfold host_semantic.append_claim_bytes_loop.body
  simp only [show i<29#usize from hi,↓reduceIte]
  rw [ProverCommitArray49.index 29#usize p i hi]
  simp only [bind_tc_ok]
  rw [show @aspis_core.field.wide_exact.WideExact.from_qm31 _
      (ProverRwP6BodyCandidate.selected ops) (p i.val)=.ok (wide (p i.val)) from embed ops _]
  simp only [bind_tc_ok]
  rw [show @aspis_core.field.wide_exact.WideExact.to_le_bytes _
      (ProverRwP6BodyCandidate.selected ops) (wide (p i.val))=
        .ok (PV_RunJoin_FlatBytes35.wire (wide (p i.val))) from
          PV_RunJoin_FlatBytes35.installed ops _]
  simp only [bind_tc_ok,lift,hnext]

#print axioms stop
#print axioms step
end R1Z.PV_RunJoin_ClaimStep41
