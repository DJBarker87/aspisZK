import R1Z.ProverRwQueryTransition
import Query31ExplicitListLoop
set_option autoImplicit false
namespace R1Z.ProverRwQueryListStep
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryTransition
open Query31ExplicitScanBody Query31ExplicitListLoop Query31ExplicitScanConcreteSteps

theorem add_wrapping (i : Usize) (bound : i.val<64) :
    (i + 1#usize : Result Usize)=ok (Usize.wrapping_add i 1#usize) := by
  obtain ⟨j,hj,hv⟩ := WP.spec_imp_exists (Usize.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
  have he : j=Usize.wrapping_add i 1#usize := by
    apply UScalar.eq_of_val_eq
    rw [wrapping_succ i bound]
    exact hv
  rwa [he] at hj

theorem body_advance (s : Query31ExplicitScanBody.CurrentScan) (x : U32) (xs : List U32)
    (hlen : s.accepted_len.val<22) (hdraw : s.draws.val<64) :
    body (stdOps listNext) (x::xs) s =
      (do let next ← advance s x; ok (.cont (xs,next))) := by
  have nf : s.accepted_len≠22#usize := by intro he; have hv:=congrArg UScalar.val he; change s.accepted_len.val=22 at hv; omega
  have nc : s.draws≠64#usize := by intro he; have hv:=congrArg UScalar.val he; change s.draws.val=64 at hv; omega
  have hb : s.accepted_len.val≤s.accepted.length := by
    simp only [Array.length,s.accepted.property]; change s.accepted_len.val≤22; omega
  obtain ⟨sl,hsl,hspec⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
      ({«end»:=s.accepted_len} : core.ops.range.RangeTo Usize)
      (Array.to_slice s.accepted) hb)
  have hprefix : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      s.accepted {«end»:=s.accepted_len}=ok sl := hsl
  have hval : (↑sl : List U32)=s.accepted.val.take s.accepted_len.val := by
    simpa [Array.to_slice,List.slice] using hspec.1
  have hc : core.slice.Slice.contains core.cmp.PartialEqU32 sl x =
      ok (decide (x.val∈acceptedPrefix s)) := by
    rw [slice_contains_eq_mem,hval]
    congr 2
    exact propext (mem_val_iff _ x).symm
  simp only [body,stdOps,listNext,bind_tc_ok,nf,nc,if_false,
    add_wrapping s.draws hdraw,add_wrapping s.accepted_len (by omega),hprefix,hc,
    advance,contains_model s x (by omega)]
  split <;> simp only [bind_tc_ok,bind_assoc_eq]

#print axioms add_wrapping
#print axioms body_advance
end R1Z.ProverRwQueryListStep
