import R1Z.PV_CB3_Op51Arbitrary
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RL_V195
set_option autoImplicit false
/-- Sequential, nonoverlapping chunk-copy content interpretation. -/
def copies (acc : List U8) : List (List U8) → List U8
  | [] => acc
  | chunk::rest => copies (acc++chunk) rest
theorem copy_acc (chunks : List (List U8)) (acc : List U8) :
    copies acc chunks=acc++chunks.flatten := by
  induction chunks generalizing acc with
  | nil => simp [copies]
  | cons c cs ih => simp only [copies,ih,List.flatten_cons,List.append_assoc]
theorem chunks_flat (chunks : List (List U8)) : copies [] chunks=chunks.flatten := by
  rw [copy_acc]; rfl
/-- Overwrite disjoint chunks of a preallocated buffer, retaining its suffix. -/
def copyBuffer (prefix suffix : List U8) : List (List U8) → List U8
  | [] => prefix++suffix
  | chunk::rest => copyBuffer (prefix++chunk) (suffix.drop chunk.length) rest
theorem copyBuffer_result (chunks : List (List U8)) (prefix suffix : List U8) :
    copyBuffer prefix suffix chunks=
      prefix++chunks.flatten++suffix.drop chunks.flatten.length := by
  induction chunks generalizing prefix suffix with
  | nil => simp [copyBuffer]
  | cons c cs ih =>
    simp only [copyBuffer,ih,List.flatten_cons,List.length_append,List.drop_drop]
    simp only [List.append_assoc]
theorem full_overwrite (chunks : List (List U8)) (h : chunks.flatten.length=32) :
    copyBuffer [] (List.replicate 32 (0#u8)) chunks=chunks.flatten := by
  rw [copyBuffer_result,h]
  simp
/-- The zip has exactly eight four-byte chunks and covers every byte once. -/
theorem slot (i j : Nat) (hi : i<8) (hj : j<4) :
    4*i+j<32 ∧ (4*i+j)/4=i ∧ (4*i+j)%4=j := by omega
theorem all_slots (k : Nat) (hk : k<32) :
    ∃ i j, i<8 ∧ j<4 ∧ k=4*i+j := by
  exact ⟨k/4,k%4,by omega,by omega,by omega⟩
theorem width_four (chunks : List (List U8))
    (hw : ∀ c ∈ chunks, c.length=4) : chunks.flatten.length=chunks.length*4 := by
  induction chunks with
  | nil => rfl
  | cons c cs ih =>
    have hc := hw c (by simp)
    have ht : ∀ x ∈ cs, x.length=4 := fun x hx => hw x (by simp [hx])
    simp only [List.flatten_cons,List.length_append,List.length_cons,ih ht,hc]
    omega
theorem eight_chunks (chunks : List (List U8)) (hn : chunks.length=8)
    (hw : ∀ c ∈ chunks, c.length=4) : chunks.flatten.length=32 := by
  rw [width_four chunks hw,hn]
/-- Complete Result transport for the unchanged serializer reference, for any carrier. -/
theorem complete [ProverRwFull.ExternalTypes] (ops : ProverRwFull.ExternalFuns)
    (x : ProverRwFull.aspis_core.field.wide_exact.WideExact) :
    (PV_CB3_Op51Source.selected ops).op51 x=PV_CB3_Op51Source.Raw.wide_bytes_flat x :=
  PV_CB3_Op51Arbitrary.op51_source ops x
theorem nonvacuous (a b c d e f g h : U32) :
    (PV_CB3_Op51Arbitrary.carrier a b c d e f g h).c1.c1.b = h := rfl
#print axioms copy_acc
#print axioms chunks_flat
#print axioms copyBuffer_result
#print axioms full_overwrite
#print axioms slot
#print axioms all_slots
#print axioms width_four
#print axioms eight_chunks
#print axioms complete
#print axioms nonvacuous
end R1Z.PV_RL_V195
