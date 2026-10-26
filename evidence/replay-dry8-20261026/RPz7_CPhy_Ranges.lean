import RPz7_SdkD_Accepted
import MultiproofConeSlices
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPhy_Ranges
open Aeneas Aeneas.Std Result
open MultiproofConeSlices OraclePortSelectedDraft

def node (proof : Slice U8) (slot : Nat) : Slice U8 :=
  if h : slot < 6 then
    sub proof (Port4B_SlotInstall.offset slot (by omega))
      (Port4B_SlotInstall.offset (slot+1) (by omega))
  else ⟨[],by simp⟩

def nodes (proof0 proof1 : Slice U8) (batch kind : Nat) : Slice U8 :=
  node (if batch = 0 then proof0 else proof1) (3*batch+kind)

def y1 (proof : Slice U8) : Slice U8 := sub proof 7031#usize 7495#usize

theorem physical (proof : Slice U8) (length : proof.val.length = 57607)
    (batch kind : Nat) (hb : batch < 2) (hk : kind < 3) :
    S2Y_OwnedChildren.PhysicalRange proof (node proof (3*batch+kind)) (3*batch+kind) ∧
    Port4B_Install.leaves.op3 proof (Usize.ofNat (3*batch+kind) (by scalar_tac)) =
      ok (node proof (3*batch+kind)) := by
  have small : 3*batch+kind < 6 := by omega
  have order := Port4B_SlotInstall.offset_step (3*batch+kind)
  have bound := Port4B_SlotInstall.offset_bound (3*batch+kind+1) (by omega)
  have read := range_total proof (Port4B_SlotInstall.offset (3*batch+kind) (by omega))
    (Port4B_SlotInstall.offset (3*batch+kind+1) (by omega))
    (by change slotStart (3*batch+kind) ≤ slotStart (3*batch+kind+1); omega)
    (by change slotStart (3*batch+kind+1) ≤ proof.val.length; omega)
  constructor
  · refine ⟨Port4B_SlotInstall.offset (3*batch+kind) (by omega),
      Port4B_SlotInstall.offset (3*batch+kind+1) (by omega),rfl,order,?_,?_⟩
    · change slotStart (3*batch+kind+1) ≤ proof.val.length; omega
    · simpa only [node,dif_pos small] using read
  · change Port4B_SlotInstall.nodeSlot proof (Usize.ofNat (3*batch+kind) _) = _
    unfold Port4B_SlotInstall.nodeSlot
    have value : (Usize.ofNat (3*batch+kind) (by scalar_tac)).val = 3*batch+kind := rfl
    simpa only [value,dif_pos small,node] using read

theorem multiproof (proof0 proof1 : Slice U8)
    (length0 : proof0.val.length = 57607) (length1 : proof1.val.length = 57607) :
    S2W_ChildJoins.MultiproofConeJoin proof0 proof1 (nodes proof0 proof1) := by
  constructor
  · intro k hk
    simpa only [nodes,if_pos rfl,ite_true] using (physical proof0 length0 0 k (by decide) hk).1
  · intro k hk
    simpa only [nodes,show ¬ (1 : Nat) = 0 from by decide,if_false] using
      (physical proof1 length1 1 k (by decide) hk).1

theorem scan (proof : Slice U8) (length : proof.val.length = 57607)
    (success : Op4P_Install.sourceBody proof = ok (.Ok ())) :
    S2W_ChildJoins.S8StageConeJoin proof (y1 proof) ∧
    Op4P_Extract.Op4P_reference.reference.check_values (y1 proof) = ok true := by
  have bound : (7495#usize).val ≤ proof.val.length := by change 7495 ≤ proof.val.length; omega
  have read := range_total proof 7031#usize 7495#usize (by decide) bound
  refine ⟨⟨by exact ⟨bound,read⟩⟩,?_⟩
  unfold Op4P_Install.sourceBody Op4P_Extract.Op4P_reference.canonical_scan at success
  obtain ⟨result,run,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ success
  cases result with
  | Err e => cases tail
  | Ok u =>
    obtain ⟨flag,run,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ run
    cases flag with
    | false => cases tail
    | true =>
      unfold Op4P_Extract.Op4P_reference.parser_reference.scan at run
      have size : Slice.len proof = 57607#usize := UScalar.eq_of_val_eq length
      simp only [size,bne_self_eq_false,Bool.false_eq_true,if_false,read,bind_tc_ok] at run
      obtain ⟨checked,call,rest⟩ := OraclePortCkptAbiTry.bind_success _ _ _ run
      cases checked with
      | false => cases rest
      | true => exact call

#print axioms physical
#print axioms multiproof
#print axioms scan
end AspisR1.CPhy_Ranges
end
