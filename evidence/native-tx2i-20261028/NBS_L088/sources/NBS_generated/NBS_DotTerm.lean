import JFs_TX2_ArrayRead
import FIo_ArrayCanon
import NBQ_RawCell
set_option autoImplicit false
noncomputable section
namespace NBS_DotTerm
open Aeneas Aeneas.Std Result ControlFlow AspisR1
abbrev NE := FIo_Install.NE
/-- Input decoding domain. It mentions no dot output or loop success. -/
def Scalars (q : Array U8 608#usize) (slot : Usize) : Prop :=
  ∀ term : Usize, term.val<26 → ∃ scalar,
    JFr_TX2_ScalarRead.read q slot term=ok scalar ∧ scalar.val<2147483647

/-- Derive the canonical eight limbs of the SAME coefficient read. -/
theorem coefficient (g : Array NE 29#usize) (hg : FIo_ArrayCanon.Holds g)
    (term : Usize) (ht : term.val<26) :
    ∃ value limbs, Array.index_usize g term=ok value ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs value=ok limbs ∧
      JFs_TX2_ArrayEight.Canon limbs := by
  obtain ⟨value,read,mem⟩ := JFs_TX2_ArrayRead.source g term (by change term.val<29;omega)
  have h := hg value mem
  refine ⟨value,_,read,rfl,?_⟩
  intro x hx
  change x∈[_,_,_,_,_,_,_,_] at hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.1.1.1
  · exact h.1.1.2
  · exact h.1.2.1
  · exact h.1.2.2
  · exact h.2.1.1
  · exact h.2.1.2
  · exact h.2.2.1
  · exact h.2.2.2

/-- All eight emitted multiply/add/write cells compose on one arbitrary
pre-state. The generic eight-limb proof is reused, not replayed concretely. -/
theorem update (g : Array NE 29#usize) (hg : FIo_ArrayCanon.Holds g)
    (term : Usize) (ht : term.val<26) (scalar : U32) (hc : scalar.val<2147483647)
    (sums : Array U64 8#usize) (n : Nat) (hn : n<4)
    (hs : JFs_TX2_ArrayEight.Bound sums n) :
    ∃ out, JFr_TX2_DotStep.update g term scalar sums=ok out ∧
      JFs_TX2_ArrayEight.Bound out (n+1) := by
  obtain ⟨value,limbs,read,words,canon⟩ := coefficient g hg term ht
  obtain ⟨out,run,bound⟩ := JFs_TX2_ArrayEight.source limbs scalar sums n canon hc hn hs
  refine ⟨out,?_,bound⟩
  rw [JFr_TX2_DotLanes.update,read,bind_tc_ok,words,bind_tc_ok,run]

/-- One real range iteration with SAME q, g and sum state; no caller-supplied
iteration result and no fixture index. -/
theorem source (q : Array U8 608#usize) (slot : Usize) (decoded : Scalars q slot)
    (g : Array NE 29#usize) (hg : FIo_ArrayCanon.Holds g)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize)
    (n : Nat) (hn : n<4) (hs : JFs_TX2_ArrayEight.Bound sums n)
    (order : iter.start.val < iter.end.val) (stop : iter.end.val≤26) :
    ∃ next out, next.start.val=iter.start.val+1 ∧ next.end=iter.end ∧
      FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter sums=
        ok (cont (next,out)) ∧ JFs_TX2_ArrayEight.Bound out (n+1) := by
  obtain ⟨scalar,read,canon⟩ := decoded iter.start (by omega)
  obtain ⟨out,run,bound⟩ := update g hg iter.start (by omega) scalar canon sums n hn hs
  obtain ⟨⟨o,next⟩,step,ho,inc,finish⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro a b;rfl)
      iter order)
  subst o
  refine ⟨next,out,inc,finish,?_,bound⟩
  rw [JFr_TX2_DotStep.body]
  simp only [JFr_TX2_DotStep.step,step,bind_tc_ok,Aeneas.Std.uncurry,read,run]

#print axioms coefficient
#print axioms update
#print axioms source
end NBS_DotTerm
