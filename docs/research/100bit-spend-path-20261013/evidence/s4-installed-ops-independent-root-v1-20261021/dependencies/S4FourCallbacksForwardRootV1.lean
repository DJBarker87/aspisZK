import S4FullCallbackForwardRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsFourCallbacksForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsHeadBatchTermsForwardRootV1 (ParsedAt)
open AspisR1FastDotsFirstTailReadTotalRootV1 (FirstReadWitness)
open AspisR1FastDotsTailReadTotalRootV1 (ReadWitness)
open AspisR1FastDotsFullCallbackForwardRootV1 (QM)
abbrev OuterFn := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact

def SlotInput (a : Array Std.U8 608#usize) (g : Array Wide 29#usize) (slot : Usize) : Prop :=
  (∀ term : Usize, term.val<26 → ParsedAt a g slot term) ∧
  ∃ (first : FirstReadWitness a g slot) (r0 : ReadWitness a g slot 0#usize)
    (r1 : ReadWitness a g slot 1#usize) (qfirst q0 q1 : QM),
    AspisR1FastDotsCurrentQmParserRootV1.parser first.bytes=.ok (some qfirst) ∧
    AspisR1FastDotsCurrentQmParserRootV1.parser r0.bytes=.ok (some q0) ∧
    AspisR1FastDotsCurrentQmParserRootV1.parser r1.bytes=.ok (some q1)

def arrayOps (base : Ops) : Ops :=
  {base with arrayFromFn := fun {T F} n callback initial =>
    AspisR1FromFnP6Generated.arrayFromFnP6 n callback initial}
def install (base : Ops) : Ops := AspisR1FastDotsFullCallbackForwardRootV1.install (arrayOps base)

theorem four_callbacks_forward
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (hcoords : ∀ j : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hslots : ∀ slot : Usize, slot.val<4 → SlotInput a g slot) :
    ∃ values : Array Wide 4#usize,
      (install base).arrayFromFn 4#usize (OuterFn (install base)) (a,g)=.ok values ∧
      (∀ x∈values.val,AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) := by
  have hcallback : ∀ current i, i.val<(4#usize).val → current=(a,g) → ∃ value next,
      (OuterFn (install base)).call_mut current i=.ok (value,next) ∧
      AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE value) ∧ next=(a,g) := by
    intro current i hi he
    subst current
    obtain ⟨hh,first,r0,r1,qfirst,q0,q1,hpf,hp0,hp1⟩ := hslots i hi
    obtain ⟨out,hcall,hcanonical⟩ := AspisR1FastDotsFullCallbackForwardRootV1.full_callback_forward
      (arrayOps base) a g i hcoords hh first r0 r1 qfirst q0 q1 hpf hp0 hp1
    exact ⟨out,(a,g),hcall,hcanonical,rfl⟩
  obtain ⟨values,hr,hc⟩ := AspisR1P6ArrayForwardRootV1.array_from_fn_forward 4#usize
    (OuterFn (install base)) (fun current _ => current=(a,g))
    (fun x => AspisR1CurrentWide.Proof.CanonicalWide (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x))
    (a,g) (by decide) rfl hcallback
  refine ⟨values,?_,hc⟩
  change AspisR1FromFnP6Generated.arrayFromFnP6 4#usize (OuterFn (install base)) (a,g)=.ok values
  exact hr

#print axioms four_callbacks_forward
end AspisR1FastDotsFourCallbacksForwardRootV1
