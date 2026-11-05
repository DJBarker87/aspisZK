import NIT_TailChain
import NIT_ControlCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_PairControl
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts
abbrev NR := NIT_ErrorTransport.NativeReply E
abbrev RU := NIT_ErrorTransport.NativeReply Unit
abbrev RP := NIT_ErrorTransport.NativeReply Powers
abbrev Scratch := alloc.vec.Vec K

/-- Data only: the actual decoded inputs, local-array addresses and SAME powers.
There is no execution/output equation or successful-child fact in this carrier. -/
structure Context where
 w : Ref W
 alpha : Ref (Array E 2#usize)
 f : Ref (Slice U8)
 ap0 : Ref Powers
 ap1 : Ref Powers
 kappa : E
 commonAddress : Nat
 lowAddress : Nat
 scratchAddress : Nat
 partsAddress : Nat

def initial : Parts := NIG_PairFrames.initial

def afterHigh (c : Context) (w : Ref W) (parts : Parts) (reply : RU) : Result NR :=
 match reply with
 | .Err e => ok (.Err e)
 | .Ok _ => NIT_TailChain.sourceTail w.value c.f.value c.ap0.value c.ap1.value parts c.kappa

def afterPartial (c : Context) (w : Ref W) (parts : Parts) (reply : RP) : Result NR := do
 match reply with
 | .Err e => ok (.Err e)
 | .Ok partials =>
   let (r,after) ← FIo_Native.weights.shared_high partials w.value c.ap0.value c.ap1.value parts
   afterHigh c w after r

def shared (c : Context) (parts : Parts) : Result NR := do
 let (w,common) ← NIG_CommonLoop.common_reference c.w.value
  (Array.repeat 16#usize NHX_FilledZero.zeroQ)
 let reply ← FIo_Native.weights.shared_partials c.f.value common
 afterPartial c ⟨c.w.address,w⟩ parts reply

def afterRegular (c : Context) (b : Bool) (parts : Parts) (reply : RU) : Result NR :=
 match reply with
 | .Err e => ok (.Err e)
 | .Ok _ => if b then shared c parts
   else NIT_TailChain.sourceTail c.w.value c.f.value c.ap0.value c.ap1.value parts c.kappa

def regular [FIo_Native.Allocation] (c : Context) (scratch : Scratch) : Result NR := do
 let b ← FIo_Native.weights.shared_two_point_guard c.w.value 2#usize
 let (reply,_,parts) ← FIo_Native.weights.process_regular_kinds c.w.value b c.alpha.value.to_slice
  c.f.value 2#usize 64#usize c.ap0.value c.ap1.value scratch initial
 afterRegular c b parts reply

def run [FIo_Native.Allocation] (c : Context) : Result NR := do
 let filled ← FIo_Native.aspis_core.r0.heap.filled FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy
  64#usize NHX_FilledZero.zeroQ
 match filled with
 | .Err _ => ok (.Err .Allocation)
 | .Ok scratch => regular c scratch

theorem slice_index (alpha : Array E 2#usize) (i : Usize) (bound : i.val<2) :
 Slice.index_usize alpha.to_slice i=ok (epick alpha i.val) := by
 have h : i.val<alpha.val.length := by rw [alpha.property];exact bound
 simp only [Slice.index_usize,Slice.getElem?_Usize_eq,Array.to_slice,epick,List.getElem?_eq_getElem h,Option.getD_some]

/-- Exact source-shaped factorization. The only supplied equalities are the two
CLOSED powers4 call results, at the SAME input array cells. -/
theorem source [FIo_Native.Allocation] (c : Context)
 (s0 : FIo_Native.weights.powers 4#usize (epick c.alpha.value 0)=ok c.ap0.value)
 (s1 : FIo_Native.weights.powers 4#usize (epick c.alpha.value 1)=ok c.ap1.value) :
 NIG_PairS2Body.reference c.w.value c.alpha.value.to_slice c.f.value c.kappa=run c := by
 unfold NIG_PairS2Body.reference run regular afterRegular shared afterPartial afterHigh
 unfold NIT_TailChain.sourceTail NIT_TailChain.zero initial NIG_PairFrames.initial
 simp only [slice_index c.alpha.value 0#usize (by decide),slice_index c.alpha.value 1#usize (by decide),
  show (0#usize).val=0 by rfl,show (1#usize).val=1 by rfl,s0,s1,bind_tc_ok]
 -- Only the Rust Result-control wrappers remain between identical callees.
 try simp only [bind_assoc_eq]
 congr 1
 funext filled
 cases filled with
 | Err e => rfl
 | Ok scratch =>
   dsimp only
   congr 1
   funext b
   congr 1
   funext result
   rcases result with ⟨reply,rest,parts⟩
   cases reply with
   | Err e => rfl
   | Ok u =>
     dsimp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
     cases b with
     | false => rfl
     | true =>
       dsimp only
       congr 1
       funext common
       rcases common with ⟨owner,cells⟩
       congr 1
       funext partials
       cases partials with
       | Err e => rfl
       | Ok values =>
         dsimp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
         congr 1
         funext high
         rcases high with ⟨reply,after⟩
         cases reply <;> rfl

#print axioms slice_index
#print axioms source
end AspisR1.NIT_PairControl
