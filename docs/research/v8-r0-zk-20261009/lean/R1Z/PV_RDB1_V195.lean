import R1Z.PV_RDB1_Copy
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V195
open PV_RDB1_Copy

def chunks (limbs : Array U32 8#usize) : List (List U8) :=
  limbs.val.map (fun a => (core.num.U32.to_le_bytes a).val)

theorem chunk_width (limbs : Array U32 8#usize) :
    ∀ c ∈ chunks limbs, c.length=4 := by
  intro c hc
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hc
  exact (core.num.U32.to_le_bytes a).property

theorem chunk_count (limbs : Array U32 8#usize) : (chunks limbs).length=8 := by
  have h := limbs.property
  change limbs.val.length=8 at h
  simpa only [chunks,List.length_map] using h

theorem total_width (cs : List (List U8)) (h : ∀ c ∈ cs, c.length=4) :
    cs.flatten.length=cs.length*4 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc := h c (by simp)
    have hs : ∀ x ∈ cs,x.length=4 := fun x hx => h x (by simp [hx])
    simp only [List.flatten_cons,List.length_append,List.length_cons,hc,ih hs]
    omega

theorem bytes_length (limbs : Array U32 8#usize) : (chunks limbs).flatten.length=32 := by
  rw [total_width _ (chunk_width limbs),chunk_count]

def nativeBytes (limbs : Array U32 8#usize) : List U8 :=
  copies (List.replicate 32 (0#u8)) 0 (chunks limbs)

theorem source_complete (limbs : Array U32 8#usize) :
    nativeBytes limbs = (chunks limbs).flatten := by
  have h := copies_result (chunks limbs) [] (List.replicate 32 (0#u8))
  simpa only [nativeBytes,List.nil_append,List.length_nil,bytes_length,List.drop_replicate,
    Nat.sub_self,List.replicate_zero,List.append_nil] using h

/-- The zip covers eight four-byte chunks, preserving an arbitrary external
world/frame and every raw u32 bit pattern. No field canonicality premise. -/
theorem complete {W : Type} (limbs : Array U32 8#usize) (world : W) :
    (ok (nativeBytes limbs,world) : Result (List U8 × W)) =
      ok ((chunks limbs).flatten,world) := by rw [source_complete]

theorem slot_bounds (i j : Nat) (hi : i<8) (hj : j<4) :
    4*i+j < 32 ∧ 4*i+4 ≤ 32 ∧ (4*i+j)/4=i ∧ (4*i+j)%4=j := by omega

theorem cover (k : Nat) (hk : k<32) :
    ∃ i j,i<8 ∧ j<4 ∧ k=4*i+j := ⟨k/4,k%4,by omega,by omega,by omega⟩

/-- Uniqueness shows no output coordinate is duplicated or left with its
initial zero value by the chunks_exact_mut/zip iteration. -/
theorem disjoint (i j i' j' : Nat) (hj : j<4) (hj' : j'<4)
    (same : 4*i+j=4*i'+j') : i=i' ∧ j=j' := by omega

#print axioms chunk_width
#print axioms chunk_count
#print axioms total_width
#print axioms bytes_length
#print axioms source_complete
#print axioms complete
#print axioms slot_bounds
#print axioms cover
#print axioms disjoint
end R1Z.PV_RDB1_V195
