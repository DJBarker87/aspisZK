import AspisR1RetainedClaimBinding.Funs
import CuSavingsRetainedSamplerPrepared
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedClaimBinding
open Aeneas Aeneas.Std Result
namespace R
abbrev E := AspisR1RhoPowerTail.aspis_core.field.WideExact
abbrev Error := AspisR1RhoPowerTail.verifier.Error
end R
namespace C
abbrev E := AspisR1CanonicalDots.field.wide_exact.WideExact
end C
open CuSavingsRetainedSamplerBinding
abbrev Raw := AspisR1RetainedClaimBinding.E

def toDot (x : R.E) : C.E := CuSavingsCanonicalDotsSources.inputToDot (input x)
def fromDot (x : C.E) : R.E := fromInput (AspisR1RetainedClaimBinding.toInput x)
def toTable (g : Array R.E 29#usize) : Array C.E 29#usize :=
  ⟨g.val.map toDot,by simp only [List.length_map,g.property]⟩
def fromError : AspisR1CanonicalDots.Error→R.Error
  | .Parse=>.Parse | .Semantic=>.Semantic | .Transcript=>.Transcript | .Relation=>.Relation
  | .Merkle=>.Merkle | .Query=>.Query | .Checkpoint=>.Checkpoint | .Allocation=>.Allocation

def result (r : core.result.Result C.E AspisR1CanonicalDots.Error) : core.result.Result R.E R.Error :=
  match r with | .Ok v=>.Ok (fromDot v) | .Err e=>.Err (fromError e)

variable [AspisR1CanonicalDots.Shared]
@[reducible] def call (isNew : Bool) (scalarAt : Usize→AspisR1CanonicalDots.VectorCommon)
    (g : Array R.E 29#usize) : AspisR1RetainedClaimBinding.DotCall where
  dot := fun point _ =>
    if isNew then @AspisR1CanonicalDots.new_callers.claim_dot _ (scalarAt point) (toTable g)
    else @AspisR1CanonicalDots.old_callers.claim_dot _ (scalarAt point) (toTable g)

variable [AspisR1RetainedClaimBinding.Trace]
def body (isNew : Bool) (scalarAt : Usize→AspisR1CanonicalDots.VectorCommon)
    (inactive : R.E) (g : Array R.E 29#usize) (kappa : R.E) :
    Result (core.result.Result R.E R.Error) := do
  let r ← @AspisR1RetainedClaimBinding.claim_context (call isNew scalarAt g) inferInstance
    (toDot inactive) (toTable g) (toDot kappa)
  .ok (result r)

theorem toTable_source (powers : Array AspisR1CanonicalInputs.field.wide_exact.WideExact 29#usize) :
    toTable (table powers)=CuSavingsCanonicalVectorLoop.dotTable powers := by
  apply Subtype.ext
  simp only [toTable,table,List.map_map]
  rfl

variable [AspisR1CanonicalSampler.Shared] [AspisR1CanonicalReader.Runtime]
theorem body_equivalence (scalarAt : Usize→AspisR1CanonicalDots.VectorCommon)
    (inactive kappa : R.E) (base : AspisR1CanonicalInputs.field.wide_exact.WideExact)
    (hb : CuSavingsCanonicalDotsSources.SourceValue base)
    (powers : Array AspisR1CanonicalInputs.field.wide_exact.WideExact 29#usize)
    (hp : AspisR1CanonicalInputs.weights.powers 29#usize base=.ok powers) :
    body true scalarAt inactive (table powers) kappa=
      body false scalarAt inactive (table powers) kappa := by
  have dots := CuSavingsCanonicalVectorContexts.six_point_claim_context
    (fun f=>f) scalarAt base hb powers hp
  have hc : call true scalarAt (table powers)=call false scalarAt (table powers) := by
    unfold call
    apply congrArg AspisR1RetainedClaimBinding.DotCall.mk
    funext point ignored
    simp only [toTable_source,if_true,Bool.false_eq_true,if_false]
    exact congrFun dots point
  unfold body
  rw [hc]

#print axioms toTable_source
#print axioms body_equivalence
end AspisR1.CuSavingsRetainedClaimBinding
