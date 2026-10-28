import NDO_JFw_TX2_DotsExplicit
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_PushStep
open Aeneas Aeneas.Std Result ControlFlow
open JFs_TX2_RawMap
abbrev plus (a b : U64) := U64.wrapping_add a (FIo_ReduceBounds.fold b)
theorem next0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
    {start:=0#usize,«end»:=4#usize}=ok (some 0#usize,{start:=1#usize,«end»:=4#usize}) := by
  obtain ⟨⟨o,n⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro a b;rfl)
      {start:=0#usize,«end»:=4#usize} (by decide))
  subst o
  have e : n.start=1#usize := UScalar.eq_of_val_eq hs
  have ne : n={start:=1#usize,«end»:=4#usize} := by
    rcases n with ⟨a,b⟩
    change a=1#usize at e
    change b=4#usize at he
    subst a;subst b;rfl
  exact ne ▸ run
theorem next1 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
    {start:=1#usize,«end»:=4#usize}=ok (some 1#usize,{start:=2#usize,«end»:=4#usize}) := by
  obtain ⟨⟨o,n⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro a b;rfl)
      {start:=1#usize,«end»:=4#usize} (by decide))
  subst o
  have e : n.start=2#usize := UScalar.eq_of_val_eq hs
  have ne : n={start:=2#usize,«end»:=4#usize} := by
    rcases n with ⟨a,b⟩
    change a=2#usize at e
    change b=4#usize at he
    subst a;subst b;rfl
  exact ne ▸ run
theorem next2 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
    {start:=2#usize,«end»:=4#usize}=ok (some 2#usize,{start:=3#usize,«end»:=4#usize}) := by
  obtain ⟨⟨o,n⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro a b;rfl)
      {start:=2#usize,«end»:=4#usize} (by decide))
  subst o
  have e : n.start=3#usize := UScalar.eq_of_val_eq hs
  have ne : n={start:=3#usize,«end»:=4#usize} := by
    rcases n with ⟨a,b⟩
    change a=3#usize at e
    change b=4#usize at he
    subst a;subst b;rfl
  exact ne ▸ run
theorem next3 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
    {start:=3#usize,«end»:=4#usize}=ok (some 3#usize,{start:=4#usize,«end»:=4#usize}) := by
  obtain ⟨⟨o,n⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro a b;rfl)
      {start:=3#usize,«end»:=4#usize} (by decide))
  subst o
  have e : n.start=4#usize := UScalar.eq_of_val_eq hs
  have ne : n={start:=4#usize,«end»:=4#usize} := by
    rcases n with ⟨a,b⟩
    change a=4#usize at e
    change b=4#usize at he
    subst a;subst b;rfl
  exact ne ▸ run
theorem next4 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
    {start:=4#usize,«end»:=4#usize}=ok (none,{start:=4#usize,«end»:=4#usize}) := by
  obtain ⟨⟨o,n⟩,run,ho,ne⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_none_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro a b;rfl)
      {start:=4#usize,«end»:=4#usize} (by decide))
  subst o
  exact ne ▸ run
theorem source0 (a b c d r0 r1 r2 r3 : U64) :
    FIo_Native.fast_pairing.canonical.Dot.push_loop.body (pack r0 r1 r2 r3)
      {start:=0#usize,«end»:=4#usize} ⟨pack a b c d⟩=ok (cont ({start:=1#usize,«end»:=4#usize},⟨pack (plus a r0) b c d⟩)) := by
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
  rw [next0]
  simp only [FIo_Native.fast_pairing.canonical.P,lift,bind_tc_ok]
  rfl
theorem source1 (a b c d r0 r1 r2 r3 : U64) :
    FIo_Native.fast_pairing.canonical.Dot.push_loop.body (pack r0 r1 r2 r3)
      {start:=1#usize,«end»:=4#usize} ⟨pack a b c d⟩=ok (cont ({start:=2#usize,«end»:=4#usize},⟨pack a (plus b r1) c d⟩)) := by
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
  rw [next1]
  simp only [FIo_Native.fast_pairing.canonical.P,lift,bind_tc_ok]
  rfl
theorem source2 (a b c d r0 r1 r2 r3 : U64) :
    FIo_Native.fast_pairing.canonical.Dot.push_loop.body (pack r0 r1 r2 r3)
      {start:=2#usize,«end»:=4#usize} ⟨pack a b c d⟩=ok (cont ({start:=3#usize,«end»:=4#usize},⟨pack a b (plus c r2) d⟩)) := by
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
  rw [next2]
  simp only [FIo_Native.fast_pairing.canonical.P,lift,bind_tc_ok]
  rfl
theorem source3 (a b c d r0 r1 r2 r3 : U64) :
    FIo_Native.fast_pairing.canonical.Dot.push_loop.body (pack r0 r1 r2 r3)
      {start:=3#usize,«end»:=4#usize} ⟨pack a b c d⟩=ok (cont ({start:=4#usize,«end»:=4#usize},⟨pack a b c (plus d r3)⟩)) := by
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
  rw [next3]
  simp only [FIo_Native.fast_pairing.canonical.P,lift,bind_tc_ok]
  rfl
theorem source4 (a b c d r0 r1 r2 r3 : U64) :
    FIo_Native.fast_pairing.canonical.Dot.push_loop.body (pack r0 r1 r2 r3)
      {start:=4#usize,«end»:=4#usize} ⟨pack a b c d⟩=ok (done ⟨pack a b c d⟩) := by
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
  rw [next4]
  simp only [FIo_Native.fast_pairing.canonical.P,lift,bind_tc_ok]
  rfl
#print axioms next0
#print axioms source0
#print axioms next1
#print axioms source1
#print axioms next2
#print axioms source2
#print axioms next3
#print axioms source3
#print axioms next4
#print axioms source4
end AspisR1.JFw_TX2_PushStep
end
