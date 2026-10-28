import PV_L2C_ChunkStep
import R1Z.PV_RunJoin_EnumerateTrace
set_option autoImplicit false
namespace PV_L2C_ChunkShape
open Aeneas Aeneas.Std Result R1Z R1Z.BuilderForestStdPort
open PV_L2C_ChunkStep

def head (s : Slice U32) : Slice U32 := ⟨s.val.take 8,by
  have := s.property; simp only [List.length_take];omega⟩
def tail (s : Slice U32) : Slice U32 := ⟨s.val.drop 8,by
  have := s.property; simp only [List.length_drop];omega⟩
def advance (i : Iter) : Iter :=
  ⟨⟨tail i.iter.remaining,8⟩,Usize.wrapping_add i.count 1#usize⟩

theorem done (i : Iter) (h : i.iter.remaining.val = []) :
    next i = ok (none,i) := by
  unfold next core.iter.adapters.enumerate.IteratorEnumerate.next
  simp only [core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next,
    BuilderForestStd.chunksNext,h,List.isEmpty_nil,ite_true,bind_tc_ok]
#print axioms done

theorem step (i : Iter) (hs : i.iter.size = 8)
    (hne : i.iter.remaining.val ≠ []) (hc : i.count.val < 24) :
    next i = ok (some (i.count,head i.iter.remaining),advance i) := by
  have hb : i.iter.remaining.val.isEmpty = false := by
    cases he : i.iter.remaining.val with
    | nil => exact False.elim (hne he)
    | cons x xs => rfl
  unfold next core.iter.adapters.enumerate.IteratorEnumerate.next
  simp only [core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next,
    BuilderForestStd.chunksNext,hb,Bool.false_eq_true,ite_false,bind_tc_ok]
  rw [PV_RunJoin_EnumerateTrace.checked_next i.count hc]
  simp only [bind_tc_ok]
  cases i
  simp only [advance,head,tail,hs]
#print axioms step

theorem head_length (s : Slice U32) : (head s).val.length ≤ 8 := by
  simp only [head,List.length_take];omega
#print axioms head_length

theorem tail_shorter (s : Slice U32) (hne : s.val ≠ []) :
    (tail s).val.length < s.val.length := by
  have hp := List.length_pos_iff.mpr hne
  simp only [tail,List.length_drop];omega
#print axioms tail_shorter

theorem advance_bound (i : Iter)
    (hb : i.count.val+i.iter.remaining.val.length ≤ 20)
    (hne : i.iter.remaining.val ≠ []) :
    (advance i).count.val + (advance i).iter.remaining.val.length ≤ 20 := by
  have hc : i.count.val < 24 := by omega
  have hn := BuilderRecordsArray.next_val i.count hc
  have hp := List.length_pos_iff.mpr hne
  simp only [advance,tail,List.length_drop]
  rw [hn]
  omega
#print axioms advance_bound

theorem head_canonical (s : Slice U32) (hc : ∀ x ∈ s.val, x.val < 2147483647) :
    ∀ x ∈ (head s).val, x.val < 2147483647 :=
  fun x hx => hc x (List.mem_of_mem_take hx)
#print axioms head_canonical

theorem tail_canonical (s : Slice U32) (hc : ∀ x ∈ s.val, x.val < 2147483647) :
    ∀ x ∈ (tail s).val, x.val < 2147483647 :=
  fun x hx => hc x (List.mem_of_mem_drop hx)
#print axioms tail_canonical
end PV_L2C_ChunkShape
