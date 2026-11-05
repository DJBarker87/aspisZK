import Lean
import RPz7_FIo_NativeFuns
import LPi_RawCallbacks
import NFN_GeometryPart02
import JGo_TX2_Range
import JGo_TX2_LoopChain
import NFS_AccumPart01
-- Retargeted LPi_RawAssociation
set_option autoImplicit false
namespace AspisR1.NGU_LPi_RawAssociation
open Aeneas Aeneas.Std Result

theorem source_eq (a b : FIo_Native.fast_pairing.canonical.Q) :
    FIo_Native.fast_pairing.canonical.Q.raw a b =
      AspisR1CanonicalQRawUnified.canonical.Q.raw a b := by
  simp only [FIo_Native.fast_pairing.canonical.Q.raw,FIo_QRaw.canonical.Q.raw,
    AspisR1CanonicalQRawUnified.canonical.Q.raw,LPi_RawCallbacks.left,
    LPi_RawCallbacks.right,LPi_RawCallbacks.pp,LPi_RawCallbacks.fold_callback,
    FIo_QRaw.canonical.P,AspisR1CanonicalQRawUnified.canonical.P]

#print axioms source_eq
end AspisR1.NGU_LPi_RawAssociation

-- Retargeted LPi_RawValues
set_option autoImplicit false
namespace AspisR1.NGU_LPi_RawValues
open Aeneas Aeneas.Std Result
abbrev Q := FIo_Native.fast_pairing.canonical.Q

def Canon (x : Q) : Prop :=
  x.val[0]!.val ≤ 2147483646 ∧ x.val[1]!.val ≤ 2147483646 ∧
  x.val[2]!.val ≤ 2147483646 ∧ x.val[3]!.val ≤ 2147483646

def spec (x y : Q) : Nat × Nat × Nat × Nat :=
  let a := x.val[0]!.val; let b := x.val[1]!.val
  let c := x.val[2]!.val; let d := x.val[3]!.val
  let e := y.val[0]!.val; let f := y.val[1]!.val
  let g := y.val[2]!.val; let h := y.val[3]!.val
  (R22RawQmProductResidues.rawC0 a b c d e f g h,
   R22RawQmProductResidues.rawC1 a b c d e f g h,
   R22RawQmProductResidues.rawC2 a b c d e f g h,
   R22RawQmProductResidues.rawC3 a b c d e f g h)

/-- Total concrete FIo raw call, with the existing repaired four-coordinate law.
No independently selected raw return or no-wrap hypothesis is supplied. -/
theorem source (x y : Q) (hx : Canon x) (hy : Canon y) : ∃ r0 r1 r2 r3 : U64,
    FIo_Native.fast_pairing.canonical.Q.raw x y = ok (Array.make 4#usize [r0,r1,r2,r3]) ∧
    (r0.val,r1.val,r2.val,r3.val) = spec x y := by
  obtain ⟨out,run⟩ := AspisR1S5QRawSourceTotality.qraw_total_of_canonical_limbs x y
    hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 hy.1 hy.2.1 hy.2.2.1 hy.2.2.2
  obtain ⟨a,b,c,d,e,f,g,h,r0,r1,r2,r3,shape,v0,v1,v2,v3,ea,eb,ec,ed,ee,ef,eg,eh⟩ :=
    AspisR1QRawActualC0V2.actual_raw_coefficients_of_input_bounds_v2 x y out run
      hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 hy.1 hy.2.1 hy.2.2.1 hy.2.2.2
  subst a; subst b; subst c; subst d; subst e; subst f; subst g; subst h
  refine ⟨r0,r1,r2,r3,?_,Prod.ext v0 (Prod.ext v1 (Prod.ext v2 v3))⟩
  rw [NGU_LPi_RawAssociation.source_eq,run,shape]

#print axioms source
end AspisR1.NGU_LPi_RawValues

-- Retargeted LPi_CheckedInputs
set_option autoImplicit false
namespace AspisR1.NGU_LPi_CheckedInputs
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues

def q (x : NQ) : FIo_Native.fast_pairing.canonical.Q :=
  Array.make 4#usize [x.c0.a,x.c0.b,x.c1.a,x.c1.b]

theorem canonical (x : NQ) (hx : canonQ x) : NGU_LPi_RawValues.Canon (q x) := by
  rcases hx with ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩
  simp only [NGU_LPi_RawValues.Canon,q,Array.make,List.getElem!_cons_zero,List.getElem!_cons_succ]
  exact ⟨by omega,by omega,by omega,by omega⟩

theorem checked (x : NQ) (hx : canonQ x) :
    FIo_Native.fast_pairing.checked_q x=ok (.Ok (q x)) := by
  rcases hx with ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩
  have l0 : x.c0.a < 2147483647#u32 := by scalar_tac
  have l1 : x.c0.b < 2147483647#u32 := by scalar_tac
  have l2 : x.c1.a < 2147483647#u32 := by scalar_tac
  have l3 : x.c1.b < 2147483647#u32 := by scalar_tac
  simp only [FIo_Native.fast_pairing.checked_q,FIo_Native.fast_pairing.limbs_of,
    bind_tc_ok,FIo_Native.fast_pairing.canonical.Q.from_limbs]
  simp [Array.index_usize,Array.make,FIo_Native.fast_pairing.canonical.P,
    h0,h1,h2,h3,q]

theorem from_wide (x : NE) : FIo_Native.fast_pairing.canonical.Q.from_wide x=
    ok (Array.make 2#usize [q x.c0,q x.c1]) := rfl

#print axioms canonical
#print axioms checked
#print axioms from_wide
end AspisR1.NGU_LPi_CheckedInputs

-- Retargeted LPf_DotWordStep
set_option autoImplicit false
namespace AspisR1.NGU_LPf_DotWordStep
open Aeneas Aeneas.Std Result

def bound : Nat := 10737418238

theorem fold_bound (raw : U64) : (FIo_ReduceBounds.fold raw).val ≤ bound := by
  rw [NFN_LPf_ReductionWord.fold_value]
  have h : raw.val < 18446744073709551616 := by scalar_tac
  unfold LPe_MersenneReduction.fold bound
  omega

/-- Actual per-coordinate wrapping addition is ordinary addition for every
reached count below the public4096 term cap, on arbitrary raw u64 inputs. -/
theorem value (sum raw : U64) (n : Nat) (hn : n < 4096)
    (hs : sum.val ≤ n*bound) :
    (U64.wrapping_add sum (FIo_ReduceBounds.fold raw)).val =
      sum.val + (FIo_ReduceBounds.fold raw).val ∧
    (U64.wrapping_add sum (FIo_ReduceBounds.fold raw)).val ≤ (n+1)*bound := by
  have hf := fold_bound raw
  have small : sum.val + (FIo_ReduceBounds.fold raw).val < UScalar.size .U64 := by
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits]
    unfold bound at *
    omega
  rw [U64.wrapping_add_val_eq,Nat.mod_eq_of_lt small]
  constructor
  · rfl
  · simpa only [Nat.add_mul,Nat.one_mul] using Nat.add_le_add hs hf

/-- Mathematical reduction of that exact word update: each raw representative
contributes its residue, including nonzero and maximal raw words. -/
theorem reduced (sum raw : U64) (n : Nat) (hn : n < 4096)
    (hs : sum.val ≤ n*bound) : ∃ z,
    FIo_Native.fast_pairing.canonical.reduce
      (U64.wrapping_add sum (FIo_ReduceBounds.fold raw)) = ok z ∧
    z.val = (sum.val + raw.val) % 2147483647 ∧ z.val < 2147483647 := by
  obtain ⟨z,run,v,c⟩ := NFN_LPf_ReductionWord.native_reduce
    (U64.wrapping_add sum (FIo_ReduceBounds.fold raw))
  refine ⟨z,run,?_,c⟩
  rw [(value sum raw n hn hs).1,NFN_LPf_ReductionWord.fold_value] at v
  rw [Nat.add_mod,LPe_MersenneReduction.fold_mod] at v
  rw [Nat.add_mod]
  exact v

#print axioms fold_bound
#print axioms value
#print axioms reduced
end AspisR1.NGU_LPf_DotWordStep

-- Retargeted LPf_DotPushStep
set_option autoImplicit false
namespace AspisR1.NGU_LPf_DotPushStep
open Aeneas Aeneas.Std Result ControlFlow
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
abbrev Raw := Array U64 4#usize

theorem source (self : Dot) (raw : Raw) (i next : Usize) (before term : U64)
    (hi : i.val < 4)
    (advance : core.iter.range.IteratorRange.next core.iter.range.StepUsize
      {start:=i,«end»:=4#usize} = ok (some i,{start:=next,«end»:=4#usize}))
    (oldRead : Array.index_usize self.sums i = ok before)
    (rawRead : Array.index_usize raw i = ok term) :
    FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw
      {start:=i,«end»:=4#usize} self =
      ok (.cont ({start:=next,«end»:=4#usize},
        ⟨self.sums.set i (U64.wrapping_add before (FIo_ReduceBounds.fold term))⟩)) := by
  obtain ⟨updated,write,same⟩ := WP.spec_imp_exists
    (Array.update_spec self.sums i
      (U64.wrapping_add before (FIo_ReduceBounds.fold term)) (by simpa using hi))
  subst updated
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
  rw [advance,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,oldRead,rawRead,bind_tc_ok,
    FIo_Native.fast_pairing.canonical.P,lift]
  change (do
    let a ← Array.update self.sums i (U64.wrapping_add before (FIo_ReduceBounds.fold term))
    ok (.cont ({start:=next,«end»:=4#usize},⟨a⟩) :
      ControlFlow (core.ops.range.Range Usize × Dot) Dot)) = _
  rw [write,bind_tc_ok]

#print axioms source
end AspisR1.NGU_LPf_DotPushStep

-- Retargeted LPf_DotPushFour
set_option autoImplicit false
namespace AspisR1.NGU_LPf_DotPushFour
open Aeneas Aeneas.Std Result ControlFlow
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
abbrev Raw := Array U64 4#usize
def update (a r : U64) : U64 := U64.wrapping_add a (FIo_ReduceBounds.fold r)

theorem source (a b c d r0 r1 r2 r3 : U64) :
    FIo_Native.fast_pairing.canonical.Dot.push_loop {start:=0#usize,«end»:=4#usize}
      ⟨Array.make 4#usize [a,b,c,d]⟩ (Array.make 4#usize [r0,r1,r2,r3]) =
      ok ⟨Array.make 4#usize [update a r0,update b r1,update c r2,update d r3]⟩ := by
  let raw : Raw := Array.make 4#usize [r0,r1,r2,r3]
  let s0 : Dot := ⟨Array.make 4#usize [a,b,c,d]⟩
  let s1 : Dot := ⟨Array.make 4#usize [update a r0,b,c,d]⟩
  let s2 : Dot := ⟨Array.make 4#usize [update a r0,update b r1,c,d]⟩
  let s3 : Dot := ⟨Array.make 4#usize [update a r0,update b r1,update c r2,d]⟩
  let s4 : Dot := ⟨Array.make 4#usize [update a r0,update b r1,update c r2,update d r3]⟩
  have t0 : FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw
      {start:=0#usize,«end»:=4#usize} s0 = ok (.cont ({start:=1#usize,«end»:=4#usize},s1)) := by
    exact NGU_LPf_DotPushStep.source s0 raw 0#usize 1#usize a r0 (by decide)
      (JGo_TX2_Range.next 0#usize 4#usize 1#usize (by decide) (by decide)) rfl rfl
  have t1 : FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw
      {start:=1#usize,«end»:=4#usize} s1 = ok (.cont ({start:=2#usize,«end»:=4#usize},s2)) := by
    exact NGU_LPf_DotPushStep.source s1 raw 1#usize 2#usize b r1 (by decide)
      (JGo_TX2_Range.next 1#usize 4#usize 2#usize (by decide) (by decide)) rfl rfl
  have t2 : FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw
      {start:=2#usize,«end»:=4#usize} s2 = ok (.cont ({start:=3#usize,«end»:=4#usize},s3)) := by
    exact NGU_LPf_DotPushStep.source s2 raw 2#usize 3#usize c r2 (by decide)
      (JGo_TX2_Range.next 2#usize 4#usize 3#usize (by decide) (by decide)) rfl rfl
  have t3 : FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw
      {start:=3#usize,«end»:=4#usize} s3 = ok (.cont ({start:=4#usize,«end»:=4#usize},s4)) := by
    exact NGU_LPf_DotPushStep.source s3 raw 3#usize 4#usize d r3 (by decide)
      (JGo_TX2_Range.next 3#usize 4#usize 4#usize (by decide) (by decide)) rfl rfl
  have t4 : FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw
      {start:=4#usize,«end»:=4#usize} s4 = ok (.done s4) := by
    unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
    rw [OccupancyRangeTraversal.next_done _ (by decide),bind_tc_ok]
    rfl
  change loop (fun state : core.ops.range.Range Usize × Dot =>
    FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw state.1 state.2)
    ({start:=0#usize,«end»:=4#usize},s0) = ok s4
  let states : Nat → core.ops.range.Range Usize × Dot
    | 0 => ({start:=0#usize,«end»:=4#usize},s0)
    | 1 => ({start:=1#usize,«end»:=4#usize},s1)
    | 2 => ({start:=2#usize,«end»:=4#usize},s2)
    | 3 => ({start:=3#usize,«end»:=4#usize},s3)
    | _ => ({start:=4#usize,«end»:=4#usize},s4)
  apply JGo_TX2_LoopChain.source _ states 4 s4
  · intro i hi
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases cases with h | h | h | h
    · subst i; exact t0
    · subst i; exact t1
    · subst i; exact t2
    · subst i; exact t3
  · exact t4

#print axioms source
end AspisR1.NGU_LPf_DotPushFour

-- Retargeted LPf_DotPushCut
set_option autoImplicit false
namespace AspisR1.NGU_LPf_DotPushCut
open Aeneas Aeneas.Std Result
abbrev Q := FIo_Native.fast_pairing.canonical.Q

/-- Source-order join of the actual raw call with the complete four-cell
update loop. The one unproved raw-call boundary remains explicit. -/
theorem source (a b : Q) (s0 s1 s2 s3 r0 r1 r2 r3 : U64)
    (rawCall : FIo_Native.fast_pairing.canonical.Q.raw a b =
      ok (Array.make 4#usize [r0,r1,r2,r3])) :
    FIo_Native.fast_pairing.canonical.Dot.push
      ⟨Array.make 4#usize [s0,s1,s2,s3]⟩ a b =
      ok ⟨Array.make 4#usize [NGU_LPf_DotPushFour.update s0 r0,NGU_LPf_DotPushFour.update s1 r1,
        NGU_LPf_DotPushFour.update s2 r2,NGU_LPf_DotPushFour.update s3 r3]⟩ := by
  unfold FIo_Native.fast_pairing.canonical.Dot.push
  rw [rawCall,bind_tc_ok]
  exact NGU_LPf_DotPushFour.source s0 s1 s2 s3 r0 r1 r2 r3

#print axioms source
end AspisR1.NGU_LPf_DotPushCut

-- Retargeted LPf_ArrayFour
set_option autoImplicit false
namespace AspisR1.NGU_LPf_ArrayFour
open Aeneas Aeneas.Std

theorem list_shape {α : Type} (xs : List α) (h : xs.length = 4) :
    ∃ a b c d, xs = [a,b,c,d] := by
  rcases xs with _ | ⟨a,xs⟩
  · simp at h
  rcases xs with _ | ⟨b,xs⟩
  · simp at h
  rcases xs with _ | ⟨c,xs⟩
  · simp at h
  rcases xs with _ | ⟨d,xs⟩
  · simp at h
  have hz : xs.length = 0 := by
    simp only [List.length_cons] at h
    omega
  cases xs with
  | nil => exact ⟨a,b,c,d,rfl⟩
  | cons e rest => simp at hz

theorem shape {α : Type} (xs : Array α 4#usize) :
    ∃ a b c d, xs = Array.make 4#usize [a,b,c,d] := by
  obtain ⟨a,b,c,d,h⟩ := list_shape xs.val (by simpa using xs.property)
  refine ⟨a,b,c,d,?_⟩
  apply Subtype.ext
  exact h

#print axioms list_shape
#print axioms shape
end AspisR1.NGU_LPf_ArrayFour

-- Retargeted LPi_DotPushTotal
set_option autoImplicit false
namespace AspisR1.NGU_LPi_DotPushTotal
open Aeneas Aeneas.Std Result

theorem source (self : FIo_Native.fast_pairing.canonical.Dot)
    (a b : NGU_LPi_RawValues.Q) (ha : NGU_LPi_RawValues.Canon a) (hb : NGU_LPi_RawValues.Canon b) :
    ∃ out, FIo_Native.fast_pairing.canonical.Dot.push self a b=ok out := by
  obtain ⟨s0,s1,s2,s3,shape⟩ := NGU_LPf_ArrayFour.shape self.sums
  obtain ⟨r0,r1,r2,r3,raw,_⟩ := NGU_LPi_RawValues.source a b ha hb
  have same : self=⟨Array.make 4#usize [s0,s1,s2,s3]⟩ := by
    cases self
    exact congrArg FIo_Native.fast_pairing.canonical.Dot.mk shape
  subst self
  exact ⟨_,NGU_LPf_DotPushCut.source a b s0 s1 s2 s3 r0 r1 r2 r3 raw⟩

#print axioms source
end AspisR1.NGU_LPi_DotPushTotal

-- Retargeted LPi_PublicPush
set_option autoImplicit false
namespace AspisR1.NGU_LPi_PublicPush
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues

theorem source (self : FIo_Native.fast_pairing.EbyKDot) (value : NE) (scalar : NQ)
    (hv : canonE value) (hq : canonQ scalar) (count : self.count.val < 4096) :
    ∃ out, FIo_Native.fast_pairing.EbyKDot.push self value scalar=ok (.Ok (),out) ∧
      out.count.val=self.count.val+1 := by
  have ca := NGU_LPi_CheckedInputs.canonical value.c0 hv.1
  have cb := NGU_LPi_CheckedInputs.canonical value.c1 hv.2
  have cq := NGU_LPi_CheckedInputs.canonical scalar hq
  obtain ⟨a,ha⟩ := NGU_LPi_DotPushTotal.source self.c0 _ _ ca cq
  obtain ⟨b,hb⟩ := NGU_LPi_DotPushTotal.source self.c1 _ _ cb cq
  have below : ¬self.count ≥ FIo_Native.fast_pairing.MAX_TERMS := by
    simp only [FIo_Native.fast_pairing.MAX_TERMS]
    scalar_tac
  have i0 : Array.index_usize (Array.make 2#usize
      [NGU_LPi_CheckedInputs.q value.c0,NGU_LPi_CheckedInputs.q value.c1]) 0#usize =
      ok (NGU_LPi_CheckedInputs.q value.c0) := rfl
  have i1 : Array.index_usize (Array.make 2#usize
      [NGU_LPi_CheckedInputs.q value.c0,NGU_LPi_CheckedInputs.q value.c1]) 1#usize =
      ok (NGU_LPi_CheckedInputs.q value.c1) := rfl
  refine ⟨⟨a,b,Usize.wrapping_add self.count 1#usize⟩,?_,?_⟩
  · simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg below,
      NGU_LPi_CheckedInputs.from_wide,bind_tc_ok,NGU_LPi_CheckedInputs.checked scalar hq,
      core.result.Result.Insts.CoreOpsTry.branch,i0,i1,ha,hb,lift]
  · rw [Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    have lim := (4096#usize).hSize
    change 4096 < UScalar.size .Usize at lim
    change self.count.val+1 < UScalar.size .Usize
    omega

#print axioms source
end AspisR1.NGU_LPi_PublicPush

-- Retargeted LPf_DotFinish
set_option autoImplicit false
namespace AspisR1.NGU_LPf_DotFinish
open Aeneas Aeneas.Std Result

/-- Compose four unconditional reducer results in the actual extracted private
Dot::finish body. The four input words are independent and unrestricted. -/
theorem source (a b c d : U64) : ∃ z0 z1 z2 z3,
    FIo_Native.fast_pairing.canonical.Dot.finish
      ⟨Array.make 4#usize [a,b,c,d]⟩ = ok (Array.make 4#usize [z0,z1,z2,z3]) ∧
    z0.val = a.val % 2147483647 ∧ z1.val = b.val % 2147483647 ∧
    z2.val = c.val % 2147483647 ∧ z3.val = d.val % 2147483647 ∧
    z0.val < 2147483647 ∧ z1.val < 2147483647 ∧
    z2.val < 2147483647 ∧ z3.val < 2147483647 := by
  obtain ⟨z0,h0,v0,c0⟩ := NFN_LPf_ReductionWord.native_reduce a
  obtain ⟨z1,h1,v1,c1⟩ := NFN_LPf_ReductionWord.native_reduce b
  obtain ⟨z2,h2,v2,c2⟩ := NFN_LPf_ReductionWord.native_reduce c
  obtain ⟨z3,h3,v3,c3⟩ := NFN_LPf_ReductionWord.native_reduce d
  refine ⟨z0,z1,z2,z3,?_,v0,v1,v2,v3,c0,c1,c2,c3⟩
  have i0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = ok a := rfl
  have i1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = ok b := rfl
  have i2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = ok c := rfl
  have i3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = ok d := rfl
  simp only [FIo_Native.fast_pairing.canonical.Dot.finish,i0,i1,i2,i3,
    bind_tc_ok,h0,h1,h2,h3]

#print axioms source
end AspisR1.NGU_LPf_DotFinish

-- Retargeted LPf_PublicDotFinish
set_option autoImplicit false
namespace AspisR1.NGU_LPf_PublicDotFinish
open Aeneas Aeneas.Std Result

/-- Both halves, the actual finalizer and its checked canonical constructor
compose on one supplied native state. Count is unrestricted and is not read. -/
theorem source (a b c d e f g h : U64) (count : Usize) : ∃ out,
    FIo_Native.fast_pairing.EbyKDot.finish
      ⟨⟨Array.make 4#usize [a,b,c,d]⟩,⟨Array.make 4#usize [e,f,g,h]⟩,count⟩ = ok out ∧
    out.c0.c0.a.val = a.val % 2147483647 ∧ out.c0.c0.b.val = b.val % 2147483647 ∧
    out.c0.c1.a.val = c.val % 2147483647 ∧ out.c0.c1.b.val = d.val % 2147483647 ∧
    out.c1.c0.a.val = e.val % 2147483647 ∧ out.c1.c0.b.val = f.val % 2147483647 ∧
    out.c1.c1.a.val = g.val % 2147483647 ∧ out.c1.c1.b.val = h.val % 2147483647 := by
  obtain ⟨a0,b0,c0,d0,r0,va,vb,vc,vd,ca,cb,cc,cd⟩ := NGU_LPf_DotFinish.source a b c d
  obtain ⟨e0,f0,g0,h0,r1,ve,vf,vg,vh,ce,cf,cg,ch⟩ := NGU_LPf_DotFinish.source e f g h
  have construct := NFS_LPf_WideConstruction.source a0 b0 c0 d0 e0 f0 g0 h0 ca cb cc cd ce cf cg ch
  let out := NFS_LPf_WideConstruction.value a0 b0 c0 d0 e0 f0 g0 h0
  refine ⟨out,?_,va,vb,vc,vd,ve,vf,vg,vh⟩
  have i0 (w x y z : U32) : Array.index_usize (Array.make 4#usize [w,x,y,z]) 0#usize = ok w := rfl
  have i1 (w x y z : U32) : Array.index_usize (Array.make 4#usize [w,x,y,z]) 1#usize = ok x := rfl
  have i2 (w x y z : U32) : Array.index_usize (Array.make 4#usize [w,x,y,z]) 2#usize = ok y := rfl
  have i3 (w x y z : U32) : Array.index_usize (Array.make 4#usize [w,x,y,z]) 3#usize = ok z := rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.finish,r0,r1,
    FIo_Native.fast_pairing.canonical.Q.limbs,bind_tc_ok,i0,i1,i2,i3,construct] <;> rfl

#print axioms source
end AspisR1.NGU_LPf_PublicDotFinish

-- Retargeted LPf_PublicDotAllStates
set_option autoImplicit false
namespace AspisR1.NGU_LPf_PublicDotAllStates
open Aeneas Aeneas.Std Result

/-- Every native accumulator carrier is included, not just a chosen history or
an empty/fixed state. This theorem still says nothing about Q.raw or push. -/
theorem source (state : FIo_Native.fast_pairing.EbyKDot) : ∃ out,
    FIo_Native.fast_pairing.EbyKDot.finish state = ok out ∧
    out.c0.c0.a.val = (state.c0.sums.val[0]!).val % 2147483647 ∧
    out.c0.c0.b.val = (state.c0.sums.val[1]!).val % 2147483647 ∧
    out.c0.c1.a.val = (state.c0.sums.val[2]!).val % 2147483647 ∧
    out.c0.c1.b.val = (state.c0.sums.val[3]!).val % 2147483647 ∧
    out.c1.c0.a.val = (state.c1.sums.val[0]!).val % 2147483647 ∧
    out.c1.c0.b.val = (state.c1.sums.val[1]!).val % 2147483647 ∧
    out.c1.c1.a.val = (state.c1.sums.val[2]!).val % 2147483647 ∧
    out.c1.c1.b.val = (state.c1.sums.val[3]!).val % 2147483647 := by
  rcases state with ⟨⟨left⟩,⟨right⟩,count⟩
  obtain ⟨a,b,c,d,hl⟩ := NGU_LPf_ArrayFour.shape left
  obtain ⟨e,f,g,h,hr⟩ := NGU_LPf_ArrayFour.shape right
  subst left
  subst right
  simpa [Array.make] using NGU_LPf_PublicDotFinish.source a b c d e f g h count

#print axioms source
end AspisR1.NGU_LPf_PublicDotAllStates

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
