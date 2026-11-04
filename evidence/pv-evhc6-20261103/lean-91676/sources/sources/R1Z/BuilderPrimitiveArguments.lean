import R1Z.BuilderPrimitiveWriters
import R1Z.BuilderRecordsFields

/-! Primitive occupancy arguments, with no admission hypothesis. -/
set_option autoImplicit false
namespace R1Z.BuilderPrimitiveArguments
open Aeneas Aeneas.Std Result R0Z.WriterRefine BuilderRecordsFields
open AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder

def wordWitness (w : RW) : RustWitness where
  inputValue := w.input_value
  outputValue := w.output_value
  changeValue := w.change_value
  sk := w.sk
  salt := w.salt
  bits := w.bits
  sibs := w.sibs
  pairFirst := w.pair_first
  pairOccupied := w.pair_occupied
  pairSecond := w.pair_second
  pairInverse := w.pair_inverse
  recipientOwner := w.recipient_owner
  recipientSalt := w.recipient_salt
  changeOwner := w.change_owner
  changeSalt := w.change_salt

def wordPublic (p : RP) : RustPublic where
  variant := if p.transfer then .privateTransfer else .withdrawal
  asset := p.asset
  nextPairIndex := p.next_pair_index.val
  frontier := p.frontier
  empty := p.empty

def inputRecord (w : RW) : AspisBuilderGlueSource.aspis_r0_writer_copies.OccRecord :=
  ⟨w.pair_occupied,w.pair_inverse,w.pair_second,w.bits.val[0]!,true⟩

theorem in_record (w : RW) : in_rec w = ok (inputRecord w) := by
  rw [in_rec,index_ok w.bits 0#usize (by decide)]
  rfl

theorem input_correspondence (w : RW) :
    BuilderPrimitiveWriters.occRecord (inputRecord w) = inRec (wordWitness w) := rfl

theorem zero_digest : ZERO8 = zero8 := by
  unfold ZERO8 zero8 arr8
  rfl

theorem aux_callee_withdrawal (w : RW) (p : RP) (hp : p.transfer = false) :
    (do
      let i ← in_rec w
      let o ← out_rec w p
      AspisBuilderGlueSource.aspis_r0_writer_copies.write_aux_block
        (Array.make 3#usize [w.input_value,w.output_value,w.change_value]) i o) =
      auxR (wordWitness w) (wordPublic p) := by
  rw [in_record,out_rec,hp]
  simp only [Bool.false_eq_true,if_false,bind_tc_ok]
  rw [BuilderPrimitiveWriters.write_aux_block]
  unfold auxR outRec wordPublic
  simp only [hp,Bool.false_eq_true,if_false]
  simp only [BuilderPrimitiveWriters.occRecord,zero_digest]
  rfl

theorem parts_aux_withdrawal (w : RW) (p : RP) (pt : Parts)
    (hp : p.transfer = false) (h : parts w p = ok pt) :
    auxR (wordWitness w) (wordPublic p) = ok pt.aux := by
  unfold parts at h
  obtain ⟨m,_,h⟩ := bind_ok_inv h
  obtain ⟨blocks,_,h⟩ := bind_ok_inv h
  obtain ⟨⟨cur,l,r⟩,_,h⟩ := bind_ok_inv h
  obtain ⟨path,_,h⟩ := bind_ok_inv h
  rw [← aux_callee_withdrawal w p hp]
  obtain ⟨i,hi,h⟩ := bind_ok_inv h
  obtain ⟨o,ho,h⟩ := bind_ok_inv h
  obtain ⟨aux,ha,h⟩ := bind_ok_inv h
  have he := congrArg Parts.aux (Result.ok.inj h)
  rw [hi,ho]
  simp only [bind_tc_ok]
  rw [ha]
  exact congrArg Result.ok he

theorem parts_aux_content_withdrawal (w : RW) (p : RP) (pt : Parts)
    (hp : p.transfer = false) (h : parts w p = ok pt) :
    pt.aux = okOr (auxR (wordWitness w) (wordPublic p)) (Array.repeat 256#usize 0#u32) := by
  rw [parts_aux_withdrawal w p pt hp h,okOr_ok]

#print axioms zero_digest
#print axioms in_record
#print axioms input_correspondence
#print axioms aux_callee_withdrawal
#print axioms parts_aux_withdrawal
#print axioms parts_aux_content_withdrawal
end R1Z.BuilderPrimitiveArguments
