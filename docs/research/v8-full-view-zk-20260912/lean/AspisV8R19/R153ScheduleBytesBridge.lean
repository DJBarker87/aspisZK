import AspisR151QuerySchedule.Funs
import AspisV8R19.R144BeforeOodBytesBridge
import AspisV8R19.R152WrappingBounds

set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace AspisV8R19.R153ScheduleBytesBridge
open Aeneas Aeneas.Std Result ControlFlow Aeneas.Std.WP
open AspisV8R19 R144BeforeOodBytesBridge R152WrappingBounds

theorem body_exact (v : Slice AspisR136BeforeOod.aspis_core.field.QM31)
    (hsize : 16 * v.val.length ≤ Usize.max)
    (iter : Iter) (b : alloc.vec.Vec U8) (h : Inv v (iter,b)) :
    AspisR151QuerySchedule.bytes_loop.body iter b = AspisR136BeforeOod.bytes_loop.body iter b := by
  simp only [R144BeforeOodBytesBridge.Inv,Prod.fst,Prod.snd] at h
  obtain ⟨hs,hi,hle,hb⟩ := h
  by_cases hlt : iter.count.val < v.val.length
  · obtain ⟨⟨o,iter1⟩,he,ho,hs1,hi1,hc1⟩ := spec_imp_exists
      (enum_next_some v iter hs hi hlt (by omega))
    have hmul : iter.count.val * 16 ≤ Usize.max := by omega
    have hstart : (Std.Usize.wrapping_mul iter.count 16#usize).val = iter.count.val * 16 := by
      have hm : (iter.count * 16#usize : Result Usize) ⦃ r => r.val = iter.count.val * 16 ⦄ := by
        apply UScalar.mul_spec
        simpa only [UScalar.max_USize_eq, show (16#usize : Usize).val = 16 from rfl] using hmul
      rw [checked_mul_eq_wrapping _ _ hmul, spec_ok] at hm
      exact hm
    have hend : (Std.Usize.wrapping_mul iter.count 16#usize).val + 16 ≤ Usize.max := by
      rw [hstart]; omega
    simp only [AspisR151QuerySchedule.bytes_loop.body,AspisR136BeforeOod.bytes_loop.body,
      he,bind_tc_ok]
    simp_all only [ho,lift,bind_tc_ok]
    rw [checked_mul_eq_wrapping iter.count 16#usize hmul]
    simp only [bind_tc_ok]
    rw [checked_add_eq_wrapping (Std.Usize.wrapping_mul iter.count 16#usize) 16#usize (by simpa only [hstart, show (16#usize : Usize).val = 16 from rfl] using hend)]
    rfl
  · have hnext : core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter AspisR136BeforeOod.aspis_core.field.QM31) iter =
          .ok (none, { iter with iter := iter.iter }) := by
      simp [core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.slice.iter.IteratorSliceIter.next, hs, hi, Slice.len, hlt]
    simp only [AspisR151QuerySchedule.bytes_loop.body,AspisR136BeforeOod.bytes_loop.body,
      hnext,bind_tc_ok]

theorem loop_spec (v : Slice AspisR136BeforeOod.aspis_core.field.QM31)
    (hsize : 16 * v.val.length ≤ Usize.max)
    (iter : Iter) (b : alloc.vec.Vec U8) (h : Inv v (iter,b)) :
    AspisR151QuerySchedule.bytes_loop iter b ⦃ out => out.val = packed v.val ⦄ := by
  unfold AspisR151QuerySchedule.bytes_loop
  apply loop.spec_decr_nat (fun p => v.val.length - p.1.count.val)
    (Inv v) (fun (out : alloc.vec.Vec U8) => out.val = packed v.val)
    (fun p => AspisR151QuerySchedule.bytes_loop.body p.1 p.2) (iter,b)
  · rintro ⟨it,buf⟩ hinv
    rw [body_exact v hsize it buf hinv]
    apply spec_mono (body_inv v hsize it buf hinv)
    intro r hr
    cases r <;> simpa only using hr
  · exact h

theorem bytes_spec (v : Slice AspisR136BeforeOod.aspis_core.field.QM31)
    (hsize : 16 * v.val.length ≤ Usize.max) :
    AspisR151QuerySchedule.bytes v ⦃ out => out.val = packed v.val ⦄ := by
  unfold AspisR151QuerySchedule.bytes
  simp only [lift]
  rw [← checked_mul_eq_wrapping (Slice.len v) 16#usize (by
    change v.val.length * 16 ≤ Usize.max; omega)]
  step with Usize.mul_spec as ⟨n,hn⟩
  step
  simp only [core.slice.Slice.iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default,bind_tc_ok]
  apply loop_spec v hsize
  simp_all [R144BeforeOodBytesBridge.Inv,packed,Slice.len,Nat.mul_comm]

theorem bytes_execution (v : Slice AspisR136BeforeOod.aspis_core.field.QM31)
    (hsize : 16 * v.val.length ≤ Usize.max) :
    AspisR151QuerySchedule.bytes v = .ok (encoded v hsize) := by
  obtain ⟨out,he,hv⟩ := spec_imp_exists (bytes_spec v hsize)
  rw [he]
  congr 1
  exact Subtype.ext hv

#print axioms body_exact
#print axioms loop_spec
#print axioms bytes_spec
#print axioms bytes_execution
end AspisV8R19.R153ScheduleBytesBridge
