import S4SevenBatchesForwardRootV1
import S4N8PackForwardRootV1
import S4HeadChainUniqueRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsHeadCoreForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsHeadBatchTermsForwardRootV1 (ParsedAt)
open AspisR1FastDotsActualInnerLoopLinearBoundV1 (cell)
open AspisR1FastDotsLimbFoldForwardRootV1 (limbCap)
open AspisR1FastDotsCurrentM31OpsBinding (withCurrentM31ParserReducer)
open AspisR1FastDotsHeadChainUniqueRootV1 (HeadCore)

def outputOps (base : Ops) : Ops :=
  {withCurrentM31ParserReducer base with
    arrayFromFn := fun {T F} n callback initial =>
      if n.val=8 then AspisR1FromFnP6Generated.arrayFromFnP6 n callback initial
      else base.arrayFromFn n callback initial
    wideFromLimbs := AspisR1FastDotsN8WideFromLimbsABI.finishFromLimbsCurrent}
def headOps (base : Ops) : Ops := AspisR1FastDotsCurrentHeadTermForwardRootV1.install (outputOps base)

theorem head_core_forward
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (hcoords : ∀ j : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hparsed : ∀ term : Usize, term.val<26 → ParsedAt a g slot term) :
    ∃ (limbs : Array Std.U64 8#usize) (values : Array Std.U32 8#usize) (body : Wide),
      HeadCore (headOps base) a g slot AspisR1FastDotsSevenBatchesForwardRootV1.initialIterator
        limbs values body ∧
      (∀ j : Fin 8, cell limbs j≤56*limbCap) ∧
      (∀ x∈values.val,x.val<AspisV8R17.RawReducer.P) := by
  obtain ⟨limbs,hi,hl,hbound⟩ := AspisR1FastDotsSevenBatchesForwardRootV1.seven_batches_forward
    (outputOps base) a g slot hcoords hparsed
  obtain ⟨values,body,ha,hcan,hpack⟩ := AspisR1FastDotsN8PackForwardRootV1.reduced_n8_pack_forward
    (headOps base) limbs
  have hm31 : withCurrentM31ParserReducer (headOps base)=headOps base := rfl
  rw [hm31] at ha
  have harray : (headOps base).arrayFromFn 8#usize
      (AspisR1FastDotsN8OutputForwardRootV1.InnerFn (headOps base)) limbs=.ok values := by
    change (if (8#usize).val=8 then AspisR1FromFnP6Generated.arrayFromFnP6 8#usize
      (AspisR1FastDotsN8OutputForwardRootV1.InnerFn (headOps base)) limbs
      else base.arrayFromFn 8#usize (AspisR1FastDotsN8OutputForwardRootV1.InnerFn (headOps base)) limbs)=.ok values
    simpa only [show (8#usize).val=8 from rfl,if_pos] using ha
  have hp : (headOps base).wideFromLimbs values=.ok (some body) := hpack
  exact ⟨limbs,values,body,⟨hi,hl,harray,hp⟩,hbound,hcan⟩

#print axioms head_core_forward
end AspisR1FastDotsHeadCoreForwardRootV1
