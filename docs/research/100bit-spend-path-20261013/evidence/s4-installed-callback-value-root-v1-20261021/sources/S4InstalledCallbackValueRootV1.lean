import S4FromLimbsSuccessCanonicalRootV1
import S4CallbackTailFinishProductV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
namespace AspisR1FastDotsInstalledCallbackValueRootV1
open AspisR1FastDotsCallbackTailProductTraceV1
open AspisR1FastDotsTailFinishSourceMapV1
open AspisR1FastDotsTailWideAddCurrentV1
open AspisR1FastDotsConcreteTailInstallRootV1
open AspisR1FastDotsCallbackTailFinishProductV1

abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Closure := AspisR1FastDotsActualCallbackTailTraceRootV1.Closure
abbrev Callback := AspisR1FastDotsActualCallbackTailTraceRootV1.Callback

/-- The same complete accepted-callback postcondition with constructor,
push, finish, packing and addition concretely installed. Scratch provenance
and the frozen Rust/P6 caller link are still separate obligations. -/
theorem installed_callback_finish_product_value
    (base : FourDotsOps) (a : Array U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (value : Wide) (closure' : Closure)
    (hcoords : ∀ j : Fin 29, CoordBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hcall : Callback (install base) (a,g) slot = .ok (value,closure')) :
    ∃ body vals wide28 q tailStart tail2 tailValue cs,
      Array.index_usize g 28#usize=.ok wide28 ∧
      (install base).wideFromLimbs vals=.ok (some body) ∧
      (install base).ebyKNew=.ok EbyKNewToPushStateABI.pushZero ∧
      (install base).ebyKPush EbyKNewToPushStateABI.pushZero wide28 q=.ok (.Ok (),tailStart) ∧
      AspisR1FastDotsActualTailLoopTraceRootV1.RunTrace
        (install base) a g slot {start:=0#usize,«end»:=2#usize}
        tailStart tail2 cs ∧
      (install base).ebyKFinish tail2=.ok tailValue ∧
      (install base).wideAdd body tailValue=.ok value ∧
      cs.map (fun c=>c.term.val)=[0,1] ∧ cs.length=2 ∧
      AspisR1DotCountBoundV1.AcceptedPushTrace
        AspisR1FastDotsPushProductTraceRootV1.raw
        EbyKNewToPushStateABI.pushZero
        ((wide28,q)::cs.map (fun c=>(c.coefficient,c.scalar))) tail2 ∧
      AspisR1FastDotsPushProductTraceRootV1.stateValue tail2=
        ((wide28,q)::cs.map (fun c=>(c.coefficient,c.scalar))).foldl
          AspisR1FastDotsPushProductTraceRootV1.addProduct
          (AspisR1FastDotsPushProductTraceRootV1.stateValue EbyKNewToPushStateABI.pushZero) ∧
      AspisR1CurrentWide.Proof.CanonicalWide (s4ToCurrentE value) ∧
      AspisR1CurrentWide.Proof.decodeWide (s4ToCurrentE value)=
        AspisR1CurrentWide.Proof.decodeWide (s4ToCurrentE body)+
        AspisR1CurrentWide.Proof.decodeWide (s4ToCurrentE tailValue) ∧
      (currentFinishWords tailValue).map (fun w=>w.val)=
        ((tail2.c0.sums.val++tail2.c1.sums.val).map
          (fun x=>x.val % AspisV8R17.RawReducer.P)) := by
  exact actual_callback_finish_product_value (install base) a g slot value closure'
    hcoords (fun _ _ _ => rfl) rfl
    (AspisR1FastDotsFromLimbsSuccessCanonicalRootV1.installed_from_limbs_success_canonical base)
    hcall

#print axioms installed_callback_finish_product_value
end AspisR1FastDotsInstalledCallbackValueRootV1
