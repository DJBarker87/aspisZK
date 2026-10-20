import AspisR1CanonicalDots.Funs
import OccupancyRangeTraversal
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalDotsCounters
open Aeneas Aeneas.Std Result ControlFlow AspisR1CanonicalDots
open OccupancyRangeTraversal
abbrev Raw := Array U64 4#usize
abbrev Q := Array U32 4#usize
abbrev Range := core.ops.range.Range Usize
variable [Shared]

def projected (sums : Raw) : new_pairing.canonical.Dot := ⟨sums⟩

def loopResult (r : Result new_pairing.canonical.Dot) : Result Raw :=
  r >>= fun x => .ok x.sums


def cell (raw sums : Raw) (j : Usize) : Result Raw := do
  let i ← Array.index_usize sums j
  let i1 ← Array.index_usize raw j
  let i4 ← i1 >>> 31#i32
  let i5 := core.num.U64.wrapping_add (i1 &&& 2147483647#u64) i4
  let i6 := core.num.U64.wrapping_add i i5
  Array.update sums j i6

theorem new_body (raw sums : Raw) (iter next : Range)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some iter.start,next)) :
    new_pairing.canonical.Dot.push_loop.body raw iter (projected sums) =
      (do let out ← cell raw sums iter.start
          .ok (.cont (next,projected out))) := by
  simp only [new_pairing.canonical.Dot.push_loop.body,hn,bind_tc_ok,
    projected,new_pairing.canonical.P,cell,bind_assoc_eq]
  rfl

theorem old_body (raw sums : Raw) (iter next : Range)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some iter.start,next)) :
    old_pairing.canonical.Dot.push_loop.body raw iter sums =
      (do let out ← cell raw sums iter.start
          .ok (.cont (next,out))) := by
  simp only [old_pairing.canonical.Dot.push_loop.body,hn,bind_tc_ok,
    old_pairing.canonical.P,cell,bind_assoc_eq]
  rfl

theorem loop_transport (fuel : Nat) (raw sums : Raw) (iter : Range)
    (he : iter.end.val=4) (hi : iter.start.val≤4)
    (hf : 4-iter.start.val=fuel) :
    loopResult (new_pairing.canonical.Dot.push_loop iter (projected sums) raw) =
      old_pairing.canonical.Dot.push_loop iter sums raw := by
  induction fuel generalizing iter sums with
  | zero =>
      have hn := next_done iter (by omega)
      simp only [new_pairing.canonical.Dot.push_loop,
        old_pairing.canonical.Dot.push_loop,loopResult]
      rw [loop,loop]
      simp only [new_pairing.canonical.Dot.push_loop.body,
        old_pairing.canonical.Dot.push_loop.body,hn,bind_tc_ok,projected]
      rfl
  | succ fuel ih =>
      obtain ⟨next,hn,hinc,hend,_⟩ := next_step iter (by omega)
      unfold new_pairing.canonical.Dot.push_loop old_pairing.canonical.Dot.push_loop loopResult
      rw [loop,loop]
      dsimp only
      rw [new_body raw sums iter next hn,old_body raw sums iter next hn]
      cases hcell : cell raw sums iter.start with
      | fail error => rfl
      | div => rfl
      | ok updated =>
          exact ih updated next (by omega) (by omega) (by omega)



theorem push_transport (self : old_pairing.canonical.Dot) (a b : Q)
    (hc : self.count.val<4096) :
    loopResult (new_pairing.canonical.Dot.push (projected self.sums) a b) =
      (old_pairing.canonical.Dot.push self a b >>= fun out => .ok out.sums) := by
  have hcmp : self.count < 4096#usize := by scalar_tac
  obtain ⟨count1,hadd,_⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=self.count) (y:=1#usize) (by scalar_tac))
  simp only [loopResult,new_pairing.canonical.Dot.push,
    old_pairing.canonical.Dot.push,hcmp,massert,↓reduceIte,hadd,
    bind_tc_ok,bind_assoc_eq]
  apply (bind_eq_iff (Shared.raw a b) _ _).mpr
  intro raw _
  have hl := loop_transport 4 raw self.sums
    {start:=0#usize,«end»:=4#usize} (by scalar_tac) (by scalar_tac) (by scalar_tac)
  cases ho : old_pairing.canonical.Dot.push_loop
      {start:=0#usize,«end»:=4#usize} self.sums raw with
  | fail error => simpa only [loopResult,ho,bind_tc_fail] using hl
  | div => simpa only [loopResult,ho,bind_tc_div] using hl
  | ok value => simpa only [loopResult,ho,bind_tc_ok] using hl

#print axioms projected
#print axioms new_body
#print axioms old_body
#print axioms loop_transport
#print axioms push_transport
end AspisR1.CuSavingsCanonicalDotsCounters
