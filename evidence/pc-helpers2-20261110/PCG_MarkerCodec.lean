import PCG_MarkerRef.Funs
import NGE_NEM_DigestInstance
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_MarkerCodec
open AspisR1.S2K

theorem read {α : Type} {n : Usize} (a : Array α n) (i : Usize) (bound : i.val < n.val) :
 Array.index_usize a i = ok (a.val[i.val]'(by have h := a.property; omega)) := by
 obtain ⟨out,hread,hvalue⟩ := WP.spec_imp_exists
   (Array.index_usize_spec a i (by simpa using bound))
 rw [hread]
 congr 1

def word (d : Array U32 8#usize) (i : Fin 8) : U32 :=
 d.val[i.val]'(by have h := d.property; change d.val.length=8 at h; omega)
def byte (w : U32) (j : Fin 4) : U8 :=
 (core.num.U32.to_le_bytes w).val[j.val]'(by
   have h := (core.num.U32.to_le_bytes w).property
   change (core.num.U32.to_le_bytes w).val.length=4 at h
   omega)
def flat (d : Array U32 8#usize) : Array U8 32#usize :=
 Array.make 32#usize [byte (word d ⟨0,by decide⟩) ⟨0,by decide⟩,byte (word d ⟨0,by decide⟩) ⟨1,by decide⟩,byte (word d ⟨0,by decide⟩) ⟨2,by decide⟩,byte (word d ⟨0,by decide⟩) ⟨3,by decide⟩,byte (word d ⟨1,by decide⟩) ⟨0,by decide⟩,byte (word d ⟨1,by decide⟩) ⟨1,by decide⟩,byte (word d ⟨1,by decide⟩) ⟨2,by decide⟩,byte (word d ⟨1,by decide⟩) ⟨3,by decide⟩,byte (word d ⟨2,by decide⟩) ⟨0,by decide⟩,byte (word d ⟨2,by decide⟩) ⟨1,by decide⟩,byte (word d ⟨2,by decide⟩) ⟨2,by decide⟩,byte (word d ⟨2,by decide⟩) ⟨3,by decide⟩,byte (word d ⟨3,by decide⟩) ⟨0,by decide⟩,byte (word d ⟨3,by decide⟩) ⟨1,by decide⟩,byte (word d ⟨3,by decide⟩) ⟨2,by decide⟩,byte (word d ⟨3,by decide⟩) ⟨3,by decide⟩,byte (word d ⟨4,by decide⟩) ⟨0,by decide⟩,byte (word d ⟨4,by decide⟩) ⟨1,by decide⟩,byte (word d ⟨4,by decide⟩) ⟨2,by decide⟩,byte (word d ⟨4,by decide⟩) ⟨3,by decide⟩,byte (word d ⟨5,by decide⟩) ⟨0,by decide⟩,byte (word d ⟨5,by decide⟩) ⟨1,by decide⟩,byte (word d ⟨5,by decide⟩) ⟨2,by decide⟩,byte (word d ⟨5,by decide⟩) ⟨3,by decide⟩,byte (word d ⟨6,by decide⟩) ⟨0,by decide⟩,byte (word d ⟨6,by decide⟩) ⟨1,by decide⟩,byte (word d ⟨6,by decide⟩) ⟨2,by decide⟩,byte (word d ⟨6,by decide⟩) ⟨3,by decide⟩,byte (word d ⟨7,by decide⟩) ⟨0,by decide⟩,byte (word d ⟨7,by decide⟩) ⟨1,by decide⟩,byte (word d ⟨7,by decide⟩) ⟨2,by decide⟩,byte (word d ⟨7,by decide⟩) ⟨3,by decide⟩]

theorem extracted (d : Array U32 8#usize) : PCG_MarkerRef.encode d = ok (flat d) := by
 simp (disch := scalar_tac) only [PCG_MarkerRef.encode,read,lift,bind_tc_ok]
 rfl

theorem flat_layout (d : Array U32 8#usize) :
 (flat d).val = d.val.flatMap (fun w => (core.num.U32.to_le_bytes w).val) := by
 rcases d with ⟨xs,hl⟩
 change xs.length=8 at hl
 rcases xs with _ | ⟨a,xs⟩
 · simp at hl
 rcases xs with _ | ⟨b,xs⟩
 · simp at hl
 rcases xs with _ | ⟨c,xs⟩
 · simp at hl
 rcases xs with _ | ⟨d,xs⟩
 · simp at hl
 rcases xs with _ | ⟨e,xs⟩
 · simp at hl
 rcases xs with _ | ⟨f,xs⟩
 · simp at hl
 rcases xs with _ | ⟨g,xs⟩
 · simp at hl
 rcases xs with _ | ⟨h,xs⟩
 · simp at hl
 have tail : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
 subst xs
 simp [flat,word,byte,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes]

/-- Representation association only; the encoder's own CLOSED row is consumed below. -/
theorem accepted_layout (d : Array U32 8#usize) :
 (DigestBytes.bytes d).val = d.val.flatMap (fun w => (core.num.U32.to_le_bytes w).val) := by
 rcases d with ⟨xs,hl⟩
 change xs.length=8 at hl
 rcases xs with _ | ⟨a,xs⟩
 · simp at hl
 rcases xs with _ | ⟨b,xs⟩
 · simp at hl
 rcases xs with _ | ⟨c,xs⟩
 · simp at hl
 rcases xs with _ | ⟨d,xs⟩
 · simp at hl
 rcases xs with _ | ⟨e,xs⟩
 · simp at hl
 rcases xs with _ | ⟨f,xs⟩
 · simp at hl
 rcases xs with _ | ⟨g,xs⟩
 · simp at hl
 rcases xs with _ | ⟨h,xs⟩
 · simp at hl
 have tail : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
 subst xs
 simp [DigestBytes.bytes,DigestBytes.fold,Array.make,Array.repeat,
   Aeneas.Std.Array.setSlice!,core.num.U32.to_le_bytes,BitVec.toLEBytes,
   List.setSlice!,List.slice]

/-- Paired law for the native encoder_reply stub, at exactly its own raw digest. -/
theorem flat_is_child (d : Array U32 8#usize) :
 PCG_MarkerRef.encode d =
 AspisR1AdapterReconstruct.aspis_statement.atomic_statement.encode_digest_canonical d := by
 have child := congrArg Prod.fst (NGE_NEM_DigestInstance.result_and_frame d ())
 have same : flat d = DigestBytes.bytes d := by
   apply Subtype.eq
   exact (flat_layout d).trans (accepted_layout d).symm
 rw [extracted,same]
 exact child.symm

theorem row_184 (marker : PCG_MarkerRef.Marker) :
 PCG_MarkerRef.encode_marker marker = ok (DigestBytes.bytes marker.nullifier) := by
 change PCG_MarkerRef.encode marker.nullifier = _
 rw [flat_is_child]
 exact congrArg Prod.fst (NGE_NEM_DigestInstance.result_and_frame marker.nullifier ())

#print axioms read
#print axioms extracted
#print axioms flat_layout
#print axioms accepted_layout
#print axioms flat_is_child
#print axioms row_184
end PCG_MarkerCodec
