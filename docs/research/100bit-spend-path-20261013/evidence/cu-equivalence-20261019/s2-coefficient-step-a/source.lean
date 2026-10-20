import CuSavingsS2SourceMask
import CuSavingsS2SourceCatalog
import CuSavingsS2SourceCommon
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceCoefficientStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1S2Groups
open CuSavingsS2SourceArrays CuSavingsS2SourceCatalog
abbrev Range := core.ops.range.Range Usize
variable [Shared]

def term (f : Slice U8) (j : Usize) (cell : E) : Result E := do
  let coefficient ← old.field f j
  field.wide_exact.WideExact.add cell coefficient

def oldUpdate (next : Range) (coeff : OldCoeffs) (group : Usize) (coefficient : E)
    (masks : Masks) (groups : Usize) :
    Result (ControlFlow (Range × Masks × OldCoeffs × Usize) (Masks × OldCoeffs × Usize)) := do
  let cell ← Array.index_usize coeff group
  let value ← field.wide_exact.WideExact.add cell coefficient
  let out ← Array.update coeff group value
  .ok (.cont (next,masks,out,groups))

theorem extend_context {A : Type} (masks : Masks) (groups group : Usize) (mask : U16)
    (k : Masks → Usize → Result A) :
    (do let (ms,n) ← extend masks groups group mask;k ms n) =
    (if group=groups then (do let ms ← Array.update masks group mask
                             let n ← groups+1#usize
                             k ms n)
     else k masks groups) := by
  unfold extend
  split
  · simp only [bind_assoc_eq]
    apply (bind_eq_iff _ _ _).mpr
    intro ms hm
    apply (bind_eq_iff _ _ _).mpr
    intro n hn
    rfl
  · rfl

theorem old_factor (w : Weights) (f : Slice U8) (iter next : Range)
    (masks : Masks) (coeff : OldCoeffs) (groups group : Usize) (mask : U16)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some iter.start,next))
    (hmask : old.grouped_inactive_pair_loop0_loop0 {start:=0#usize,«end»:=16#usize} w iter.start 0#u16 = .ok mask)
    (hsearch : old.grouped_inactive_pair_loop0_loop1 masks groups mask 0#usize = .ok group) :
    old.grouped_inactive_pair_loop0.body w f iter masks coeff groups =
      (do let coefficient ← old.field f iter.start
          let (ms,n) ← extend masks groups group mask
          oldUpdate next coeff group coefficient ms n) := by
  simp only [old.grouped_inactive_pair_loop0.body,hn,bind_tc_ok]
  change (do
    let mask ← old.grouped_inactive_pair_loop0_loop0 {start:=0#usize,«end»:=16#usize} w iter.start 0#u16
    let coefficient ← old.field f iter.start
    let group ← old.grouped_inactive_pair_loop0_loop1 masks groups mask 0#usize
    if group=groups then
      let ms ← Array.update masks group mask
      let n ← groups+1#usize
      oldUpdate next coeff group coefficient ms n
    else oldUpdate next coeff group coefficient masks groups) = _
  rw [hmask,bind_tc_ok]
  apply (bind_eq_iff _ _ _).mpr
  intro coefficient hc
  rw [hsearch,bind_tc_ok,extend_context]

theorem old_body (w : Weights) (f : Slice U8) (iter next : Range)
    (masks masks1 : Masks) (coeff : OldCoeffs) (groups group groups1 : Usize) (mask : U16)
    (hg : group.val<12)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some iter.start,next))
    (hmask : old.grouped_inactive_pair_loop0_loop0 {start:=0#usize,«end»:=16#usize} w iter.start 0#u16 = .ok mask)
    (hsearch : old.grouped_inactive_pair_loop0_loop1 masks groups mask 0#usize = .ok group)
    (hext : extend masks groups group mask = .ok (masks1,groups1)) :
    old.grouped_inactive_pair_loop0.body w f iter masks coeff groups =
      (do let value ← term f iter.start (lookup coeff zero group.val)
          .ok (.cont (next,masks1,coeff.set group value,groups1))) := by
  rw [old_factor w f iter next masks coeff groups group mask hn hmask hsearch]
  simp only [hext,bind_tc_ok,oldUpdate,read coeff zero group (by scalar_tac),
    update coeff group _ (by scalar_tac),term,bind_assoc_eq]

theorem new_body (f : Slice U8) (iter next : Range) (coeff : NewCoeffs)
    (g8 : U8) (group : Usize) (hg : group.val<12)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some iter.start,next))
    (hgroup : Array.index_usize new.S2_INACTIVE_GROUPS iter.start = .ok g8)
    (hcast : UScalar.cast .Usize g8=group) :
    new.s2_grouped_inactive_pair_loop0.body f iter coeff =
      (do let value ← term f iter.start (lookup coeff zero group.val)
          .ok (.cont (next,coeff.set group value))) := by
  simp only [new.s2_grouped_inactive_pair_loop0.body,hn,bind_tc_ok]
  change (do
    let g8 ← Array.index_usize new.S2_INACTIVE_GROUPS iter.start
    let group ← lift (UScalar.cast .Usize g8)
    let cell ← Array.index_usize coeff group
    let coefficient ← new.field f iter.start
    let value ← field.wide_exact.WideExact.add cell coefficient
    let out ← Array.update coeff group value
    Result.ok (ControlFlow.cont (β:=NewCoeffs) (next,out))) = _
  simp only [hgroup,lift,hcast,bind_tc_ok,read coeff zero group (by scalar_tac),
    update coeff group _ (by scalar_tac),CuSavingsS2SourceCommon.field_eq,term,bind_assoc_eq]

#print axioms extend_context
#print axioms old_factor
#print axioms old_body
#print axioms new_body
end AspisR1.CuSavingsS2SourceCoefficientStep
