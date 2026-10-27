import LPi_PublicPush
import LPf_PublicDotAllStates
set_option autoImplicit false
namespace AspisR1.LPm_PublicState
open Aeneas Aeneas.Std Result LPi_FieldValues
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
abbrev Raw := Array U64 4#usize

def update (s : Dot) (r : Raw) : Dot :=
  ⟨Array.make 4#usize [
    LPf_DotPushFour.update s.sums.val[0]! r.val[0]!,
    LPf_DotPushFour.update s.sums.val[1]! r.val[1]!,
    LPf_DotPushFour.update s.sums.val[2]! r.val[2]!,
    LPf_DotPushFour.update s.sums.val[3]! r.val[3]!]⟩

def values (r : Raw) : Nat×Nat×Nat×Nat :=
  (r.val[0]!.val,r.val[1]!.val,r.val[2]!.val,r.val[3]!.val)

/-- Strengthen inherited totality to the SAME raw values and SAME four
updated state words. The raw-call observation is derived, never supplied. -/
theorem private_source (s : Dot) (a b : LPi_RawValues.Q)
    (ha : LPi_RawValues.Canon a) (hb : LPi_RawValues.Canon b) :
    ∃ r : Raw, FIo_Native.fast_pairing.canonical.Q.raw a b=ok r ∧
      values r=LPi_RawValues.spec a b ∧
      FIo_Native.fast_pairing.canonical.Dot.push s a b=ok (update s r) := by
  obtain ⟨s0,s1,s2,s3,shape⟩ := LPf_ArrayFour.shape s.sums
  obtain ⟨r0,r1,r2,r3,raw,meaning⟩ := LPi_RawValues.source a b ha hb
  have same : s=⟨Array.make 4#usize [s0,s1,s2,s3]⟩ := by
    cases s
    exact congrArg FIo_Native.fast_pairing.canonical.Dot.mk shape
  subst s
  refine ⟨Array.make 4#usize [r0,r1,r2,r3],raw,meaning,?_⟩
  simpa only [update,Array.make,List.getElem!_cons_zero,List.getElem!_cons_succ] using
    LPf_DotPushCut.source a b s0 s1 s2 s3 r0 r1 r2 r3 raw

/-- Public push with both actual half-products and complete state updates.
Canonicality and count are the existing public caller domain. -/
theorem source (s : FIo_Native.fast_pairing.EbyKDot) (value : NE) (scalar : NQ)
    (hv : canonE value) (hq : canonQ scalar) (count : s.count.val<4096) :
    ∃ (lo hi : Raw) (out : FIo_Native.fast_pairing.EbyKDot),
      FIo_Native.fast_pairing.EbyKDot.push s value scalar=ok (.Ok (),out) ∧
      values lo=LPi_RawValues.spec (LPi_CheckedInputs.q value.c0) (LPi_CheckedInputs.q scalar) ∧
      values hi=LPi_RawValues.spec (LPi_CheckedInputs.q value.c1) (LPi_CheckedInputs.q scalar) ∧
      out.c0=update s.c0 lo ∧ out.c1=update s.c1 hi ∧ out.count.val=s.count.val+1 := by
  have ca := LPi_CheckedInputs.canonical value.c0 hv.1
  have cb := LPi_CheckedInputs.canonical value.c1 hv.2
  have cq := LPi_CheckedInputs.canonical scalar hq
  obtain ⟨lo,_,lov,left⟩ := private_source s.c0 _ _ ca cq
  obtain ⟨hi,_,hiv,right⟩ := private_source s.c1 _ _ cb cq
  have below : ¬s.count ≥ FIo_Native.fast_pairing.MAX_TERMS := by
    simp only [FIo_Native.fast_pairing.MAX_TERMS]
    scalar_tac
  have i0 : Array.index_usize (Array.make 2#usize
      [LPi_CheckedInputs.q value.c0,LPi_CheckedInputs.q value.c1]) 0#usize =
      ok (LPi_CheckedInputs.q value.c0) := rfl
  have i1 : Array.index_usize (Array.make 2#usize
      [LPi_CheckedInputs.q value.c0,LPi_CheckedInputs.q value.c1]) 1#usize =
      ok (LPi_CheckedInputs.q value.c1) := rfl
  let out : FIo_Native.fast_pairing.EbyKDot :=
    ⟨update s.c0 lo,update s.c1 hi,Usize.wrapping_add s.count 1#usize⟩
  have call : FIo_Native.fast_pairing.EbyKDot.push s value scalar=ok (.Ok (),out) := by
    simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg below,
      LPi_CheckedInputs.from_wide,bind_tc_ok,LPi_CheckedInputs.checked scalar hq,
      core.result.Result.Insts.CoreOpsTry.branch,i0,i1,left,right,lift]
    rfl
  obtain ⟨other,otherCall,otherCount⟩ := LPi_PublicPush.source s value scalar hv hq count
  have unique : out=other := congrArg Prod.snd (Result.ok.inj (call.symm.trans otherCall))
  exact ⟨lo,hi,out,call,lov,hiv,rfl,rfl,by rw [unique]; exact otherCount⟩

#print axioms private_source
#print axioms source
end AspisR1.LPm_PublicState
