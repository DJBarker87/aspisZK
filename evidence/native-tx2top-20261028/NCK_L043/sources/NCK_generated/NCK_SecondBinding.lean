import NCK_Stage2Shape
import NCK_SnapshotRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_SecondBinding
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
/-- Conditional accepted-run binding at the exact wrapper. Every input below
comes from that SAME accepted body, original proof account0 and checkpoint6.
This theorem does not produce wrapper acceptance or cross-TX persistence. -/
theorem original_inputs {A : Type} (ops : _root_.AdapterRw.Ops)
    (allocator : Allocator A) (e : Entry)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state final : A)
    (after : Heap (Nat → Record))
    (scanner : NCK_ScanDependency.ScannerLength ops)
    (accepted : second (_root_.AdapterRw.r1_pool_adapter.owned.stage2_owned ops)
      allocator e program data slot state = ok (.Ok (after,final))) :
    ∃ pub : Array U8 1880#usize, ∃ selected cp,
      ops.op11 (_root_.AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        (Array.to_slice pub) selected cp () none = ok (.Ok ()) ∧
      selected.val = (e.buffers (e.handles 0).1).val.drop 688 ∧
      selected.val.length = 57607 ∧
      cp.val = (e.buffers (e.handles 6).1).val ∧ cp.val.length = 1768 ∧
      (e.buffers (e.handles 0).1).val.length = 58295 ∧ after = e.heap := by
  obtain ⟨body,frame⟩ := second_accepted
    (_root_.AdapterRw.r1_pool_adapter.owned.stage2_owned ops)
    allocator e program data slot state final after accepted
  obtain ⟨pa,ca,raw,cp,pub,selected,paIndex,caIndex,rawRead,cpRead,range,tx2,rawLength⟩ :=
    NCK_Stage2Shape.fixed_range ops program (e.second secondSizes) data slot scanner body
  have paSame := Result.ok.inj ((NCK_SnapshotRead.proof_index e).symm.trans paIndex)
  have caSame := Result.ok.inj ((NCK_SnapshotRead.checkpoint_index e).symm.trans caIndex)
  subst pa; subst ca
  have rawOriginal := NCK_SnapshotRead.original_bytes ops e 0 58295 58295 raw rawRead
  have cpOriginal := NCK_SnapshotRead.original_bytes ops e 6 1768 1768 cp cpRead
  have suffix := NCK_ProofSuffix.exact_suffix raw selected rawLength range
  have originalLength : (e.buffers (e.handles 0).1).val.length = 58295 := by
    rw [←rawOriginal.1]; exact rawLength
  have cpLength : cp.val.length = 1768 := by
    rw [cpOriginal.1]
    exact cpOriginal.2.elim id id
  exact ⟨pub,selected,cp,tx2,suffix.1.trans (congrArg (List.drop 688) rawOriginal.1),
    suffix.2.1,cpOriginal.1,cpLength,originalLength,frame⟩
#print axioms original_inputs
end AspisR1.NCK_SecondBinding
end
