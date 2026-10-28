import R1Z.PV_RunJoin_FlatBytes35
import R1Z.PV_RunJoin_ByteAppend38
import R1Z.PV_RunJoin_MergeArray35
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WideStep38
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev W := aspis_core.field.wide_exact.WideExact

def input (size : Usize) (f : Nat → W) :=
  Array.to_slice (ProverCommitArray49.array size f)

theorem input_size (size : Usize) (f : Nat → W) : Slice.len (input size f)=size := by
  apply UScalar.eq_of_val_eq
  simp only [input,Slice.len,Array.to_slice,ProverCommitArray49.array,List.length_ofFn]
  scalar_tac

theorem increment (size k : Usize) (hk : k.val<size.val) :
    (Usize.wrapping_add k 1#usize).val=k.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  change (k.val+1)%UScalar.size .Usize=k.val+1
  apply Nat.mod_eq_of_lt
  have big := size.hSize
  omega

theorem stop (ops : ExternalFuns) (size : Usize) (f : Nat → W)
    (bytes : alloc.vec.Vec U8) (k : Usize) (hk : ¬k.val<size.val) :
    @prover.encoded_slice_loop.body _ (ProverRwP6BodyCandidate.selected ops)
      (input size f) bytes k = .ok (.done bytes) := by
  simp only [prover.encoded_slice_loop.body,input_size,show ¬k<size from hk,↓reduceIte]

theorem step (ops : ExternalFuns) (size : Usize) (f : Nat → W)
    (bytes : alloc.vec.Vec U8) (k : Usize) (hk : k.val<size.val)
    (room : bytes.length+32≤Usize.max) :
    ∃ next,
      @prover.encoded_slice_loop.body _ (ProverRwP6BodyCandidate.selected ops)
        (input size f) bytes k = .ok (.cont (next,Usize.wrapping_add k 1#usize)) ∧
      next.val = bytes.val ++ (PV_RunJoin_FlatBytes35.wire (f k.val)).val := by
  have hroom : bytes.length+(Array.to_slice (PV_RunJoin_FlatBytes35.wire (f k.val))).length≤Usize.max := by
    have len := (PV_RunJoin_FlatBytes35.wire (f k.val)).property
    change bytes.length+(PV_RunJoin_FlatBytes35.wire (f k.val)).val.length≤Usize.max
    rw [len]
    exact room
  obtain ⟨next,hnext,hval⟩ := PV_RunJoin_ByteAppend38.append bytes
    (Array.to_slice (PV_RunJoin_FlatBytes35.wire (f k.val))) hroom
  refine ⟨next,?_,hval⟩
  unfold prover.encoded_slice_loop.body
  simp only [input_size,show k<size from hk,↓reduceIte]
  have hread : Slice.index_usize (input size f) k=.ok (f k.val) :=
    PV_RunJoin_MergeArray35.slice_values size f k hk
  rw [hread]
  simp only [bind_tc_ok]
  have hw : @aspis_core.field.wide_exact.WideExact.to_le_bytes _
      (ProverRwP6BodyCandidate.selected ops) (f k.val)=
      .ok (PV_RunJoin_FlatBytes35.wire (f k.val)) := PV_RunJoin_FlatBytes35.installed ops _
  simp only [hw,bind_tc_ok,lift,hnext]

#print axioms input_size
#print axioms increment
#print axioms stop
#print axioms step
end R1Z.PV_RunJoin_WideStep38
