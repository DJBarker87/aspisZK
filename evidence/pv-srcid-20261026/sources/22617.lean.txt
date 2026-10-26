/- Namespace port of BuilderAuxContent: same symbolic proof, actual forest extraction. -/
import R1Z.PV_Src_Forest_DigestTotal
import R1Z.PV_Src_Forest_PartsContent

/-! Complete auxiliary Parts content, for both transfer and withdrawal.
The change digest and occupancy inverse are derived from actual callees. -/
set_option autoImplicit false
namespace R1Z.PV_Src_Forest_AuxContent
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments PV_Src_Forest_DigestArguments BuilderRecordsFields
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder

theorem note_digest (w : RW) (p : RP) (h : Usize) :
    note_digest_r w p h = noteDigestR (chunksOf (wordWitness w) (wordPublic p)) h.val := by
  simp only [note_digest_r,noteDigestR,pre_state,chunk,chunk_len w p,bind_tc_ok,sponge_digest]

theorem change_digest (w : RW) (p : RP) : change_dr w p = changeDR (wordWitness w) (wordPublic p) := by
  rw [change_dr,note_digest];rfl

theorem recipient_digest (w : RW) (p : RP) : recip_dr w p = recipDR (wordWitness w) (wordPublic p) := by
  rw [recip_dr,note_digest];rfl

theorem input_digest (w : RW) (p : RP) : input_leaf_r w p = inputLeafR (wordWitness w) (wordPublic p) := by
  rw [input_leaf_r,note_digest];rfl

theorem output_record (w : RW) (p : RP) :
    ∃ out, out_rec w p = ok out ∧
      PV_Src_Forest_PrimitiveWriters.occRecord out = outRec (wordWitness w) (wordPublic p) := by
  cases hp : p.transfer with
  | false =>
    refine ⟨⟨0#u32,0#u32,ZERO8,0#u32,false⟩,?_,?_⟩
    · rw [out_rec,hp];rfl
    · simp only [outRec,wordPublic,hp,Bool.false_eq_true,if_false,
        PV_Src_Forest_PrimitiveWriters.occRecord,zero_digest]
  | true =>
    obtain ⟨d,hd⟩ := PV_Src_Forest_DigestTotal.note_total (chunksOf (wordWitness w) (wordPublic p)) 32
    have hc : changeDR (wordWitness w) (wordPublic p) = ok d := hd
    refine ⟨⟨1#u32,invR d.val[7]!,d,0#u32,false⟩,?_,?_⟩
    · rw [out_rec,hp]
      simp only [if_true,change_digest,hc,bind_tc_ok]
      rw [index_ok d 7#usize (by decide)]
      simp only [bind_tc_ok,PV_Src_Forest_InverseResult.inverse,UScalar.ofNatCore_val_eq]
    · have hv : (wordPublic p).variant = .privateTransfer := by simp [wordPublic,hp]
      simp only [outRec,hv,hc,okOr_ok,PV_Src_Forest_PrimitiveWriters.occRecord]

theorem aux_callee (w : RW) (p : RP) :
    (do let i ← in_rec w
        let o ← out_rec w p
        BuilderForestAdmissionPort.aspis_r0_writer_copies.write_aux_block
          (Array.make 3#usize [w.input_value,w.output_value,w.change_value]) i o) =
      auxR (wordWitness w) (wordPublic p) := by
  obtain ⟨out,ho,hmodel⟩ := output_record w p
  rw [in_record,ho]
  simp only [bind_tc_ok,PV_Src_Forest_PrimitiveWriters.write_aux_block]
  rw [input_correspondence,hmodel]
  rfl

theorem parts_aux (w : RW) (p : RP) (pt : Parts) (h : parts w p = ok pt) :
    auxR (wordWitness w) (wordPublic p) = ok pt.aux := by
  unfold parts at h
  obtain ⟨m,_,h⟩ := bind_ok_inv h
  obtain ⟨blocks,_,h⟩ := bind_ok_inv h
  obtain ⟨⟨cur,l,r⟩,_,h⟩ := bind_ok_inv h
  obtain ⟨path,_,h⟩ := bind_ok_inv h
  rw [← aux_callee]
  obtain ⟨i,hi,h⟩ := bind_ok_inv h
  obtain ⟨o,ho,h⟩ := bind_ok_inv h
  obtain ⟨aux,ha,h⟩ := bind_ok_inv h
  have he := congrArg Parts.aux (Result.ok.inj h)
  rw [hi,ho]
  simp only [bind_tc_ok]
  rw [ha]
  exact congrArg Result.ok he

theorem parts_aux_content (w : RW) (p : RP) (pt : Parts) (h : parts w p = ok pt) :
    pt.aux = okOr (auxR (wordWitness w) (wordPublic p)) (Array.repeat 256#usize 0#u32) := by
  rw [parts_aux w p pt h,okOr_ok]

#print axioms note_digest
#print axioms change_digest
#print axioms recipient_digest
#print axioms input_digest
#print axioms output_record
#print axioms aux_callee
#print axioms parts_aux
#print axioms parts_aux_content
end R1Z.PV_Src_Forest_AuxContent
