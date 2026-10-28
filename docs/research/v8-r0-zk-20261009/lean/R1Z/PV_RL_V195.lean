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
/-- The zip has exactly eight four-byte chunks and covers every byte once. -/
theorem slot (i j : Nat) (hi : i<8) (hj : j<4) :
    4*i+j<32 ∧ (4*i+j)/4=i ∧ (4*i+j)%4=j := by omega
/-- Complete Result transport for the unchanged serializer reference, for any carrier. -/
theorem complete [ProverRwFull.ExternalTypes] (ops : ProverRwFull.ExternalFuns)
    (x : ProverRwFull.aspis_core.field.wide_exact.WideExact) :
    (PV_CB3_Op51Source.selected ops).op51 x=PV_CB3_Op51Source.Raw.wide_bytes_flat x :=
  PV_CB3_Op51Arbitrary.op51_source ops x
theorem nonvacuous (a b c d e f g h : U32) :
    (PV_CB3_Op51Arbitrary.carrier a b c d e f g h).c1.c1.b = h := rfl
#print axioms copy_acc
#print axioms chunks_flat
#print axioms slot
#print axioms complete
#print axioms nonvacuous
end R1Z.PV_RL_V195
