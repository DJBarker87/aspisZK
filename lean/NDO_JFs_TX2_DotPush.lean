import RPu_JFs_TX2_Raw
import RPt_JFs_TX2_ArrayRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_DotPush
open Aeneas Aeneas.Std Result ControlFlow
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
abbrev Range := core.ops.range.Range Usize

theorem loop (raw : Array U64 4#usize) (self : Dot) :
    ∃ out, FIo_Native.fast_pairing.canonical.Dot.push_loop {start:=0#usize,«end»:=4#usize} self raw=ok out := by
  have spec : FIo_Native.fast_pairing.canonical.Dot.push_loop {start:=0#usize,«end»:=4#usize} self raw
      ⦃ _ => True ⦄ := by
    unfold FIo_Native.fast_pairing.canonical.Dot.push_loop
    refine Aeneas.Std.loop.spec_decr_nat
      (fun s : Range × Dot => 4-s.1.start.val)
      (fun s : Range × Dot => s.1.end.val=4 ∧ s.1.start.val≤4)
      (fun _ => True)
      (fun (r,s) => FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw r s)
      ({start:=0#usize,«end»:=4#usize},self) ?_ (by change (4#usize).val=4 ∧ (0#usize).val≤4;constructor <;> decide)
    rintro ⟨r,s⟩ ⟨he,hs⟩
    dsimp only at he hs
    unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
    simp only [lift,bind_tc_ok]
    by_cases running : r.start.val < r.end.val <;> step*
    all_goals simp_all
    all_goals scalar_tac
  obtain ⟨out,run,_⟩ := WP.spec_imp_exists spec
  exact ⟨out,run⟩

theorem source (self : Dot) (a b : FIo_Native.fast_pairing.canonical.Q) :
    ∃ out, FIo_Native.fast_pairing.canonical.Dot.push self a b=ok out := by
  obtain ⟨raw,hr⟩ := JFs_TX2_Raw.source a b
  obtain ⟨out,ho⟩ := loop raw self
  exact ⟨out,by simp only [FIo_Native.fast_pairing.canonical.Dot.push,hr,bind_tc_ok,ho]⟩

#print axioms loop
#print axioms source
end AspisR1.JFs_TX2_DotPush
end
