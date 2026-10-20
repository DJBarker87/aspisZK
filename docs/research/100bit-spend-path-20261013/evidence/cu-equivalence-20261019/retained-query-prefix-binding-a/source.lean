import CuSavingsRetainedResumeDotBinding
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedQueryPrefixBinding
open Aeneas Aeneas.Std Result
namespace Q
abbrev E := AspisR1RhoQuery.aspis_core.field.WideExact
abbrev D := AspisR1RhoQuery.aspis_core.Digest32
abbrev View := AspisR1RhoQuery.verifier.View
abbrev Prepared := AspisR1RhoQuery.verifier.Prepared
abbrev Phase := AspisR1RhoQuery.verifier.Phase
abbrev Error := AspisR1RhoQuery.verifier.Error
abbrev Geometry := AspisR1RhoQuery.QueryGeometry
end Q
abbrev DotE := CuSavingsRetainedDotsBinding.E
abbrev G := Array Q.E 29#usize
abbrev Values := Array DotE 4#usize

def variant : AspisR1RhoQuery.transport.Variant→AspisR1CuQuery.transport.Variant
  | .S1=>.S1 | .S2=>.S2 | .D=>.D
def wide (e : Q.E) : AspisR1CuQuery.field.WideExact :=
  ⟨⟨⟨e.c0.c0.a,e.c0.c0.b⟩,⟨e.c0.c1.a,e.c0.c1.b⟩⟩,⟨⟨e.c1.c0.a,e.c1.c0.b⟩,⟨e.c1.c1.a,e.c1.c1.b⟩⟩⟩
def view (v : Q.View) : AspisR1CuQuery.verifier.View :=
  {variant:=variant v.variant,semantic:=v.semantic,y1:=v.y1,inactive:=wide v.inactive,
   round0:=v.round0,folded_root:=v.folded_root,round1:=v.round1,final_message:=v.final_message,query_bytes:=v.query_bytes}

/-- Unchanged exact source pieces before and after the sole dot call.
Authentication includes the original Merkle mark; fold includes all traces,
folding and error checks, with no access to gamma. No proposition fields. -/
structure Boundaries where
  queryIndex : Q.Prepared→Usize→Result Usize
  authenticate : {H : Type}→Q.D H→Q.View→Q.Prepared→H→Option (Q.Phase→Result Unit)→Q.Geometry→Usize→Usize→Slice U8→Result (core.result.Result Unit Q.Error)
  fold : {H : Type}→Q.D H→Q.View→Q.Prepared→H→Option (Q.Phase→Result Unit)→Q.Geometry→Usize→Usize→Slice U8→Values→Result (core.result.Result (Usize×Q.E) Q.Error)

variable [AspisR1CanonicalDots.Shared]
def sourcePrefix (B : Boundaries) (dot : AspisR1RetainedDots.Shared)
    (kernel : AspisR1RetainedDots.Shared→Slice U8→CuSavingsRetainedDotsTail.G→Result Values)
    {H : Type} (D : Q.D H) (v : Q.View) (p : Q.Prepared) (g : G) (hash : H)
    (obs : Option (Q.Phase→Result Unit)) (geometry : Q.Geometry) (i : Usize) :
    Result (core.result.Result (Usize×Q.E) Q.Error) := do
  let u←B.queryIndex p i
  let q←AspisR1CuQuery.verifier.View.query (view v) i
  let authenticated←B.authenticate D v p hash obs geometry i u q
  match authenticated with
  | .Err error=>.ok (.Err error)
  | .Ok _=>
    let dots←kernel dot q (CuSavingsRetainedDotsInputs.gamma (CuSavingsRetainedResumeDotBinding.preparedTable g))
    B.fold D v p hash obs geometry i u q dots

@[reducible] def newBinding (common : AspisR1RhoQuery.QueryCommon) (B : Boundaries)
    (dot : AspisR1RetainedDots.Shared) : AspisR1RhoQuery.QueryCommon :=
  {common with queryPrefix:=sourcePrefix B (CuSavingsRetainedDotsBinding.newShared dot)
    (@AspisR1RetainedDots.prefix_new_dots.four_dots)}
@[reducible] def oldBinding (common : AspisR1RhoQuery.QueryCommon) (B : Boundaries)
    (dot : AspisR1RetainedDots.Shared) : AspisR1RhoQuery.QueryCommon :=
  {common with queryPrefix:=sourcePrefix B (CuSavingsRetainedDotsBinding.oldShared dot)
    (@AspisR1RetainedDots.old_dots.four_dots)}

variable [AspisR1CanonicalSampler.Shared] [AspisR1CanonicalReader.Runtime]
  [AspisR1CanonicalKReader.Runtime] [AspisR1CuRho.ScalarKBlocks]
def SourceTable (g : G) : Prop :=
  ∀ i (hi : i<29),CuSavingsCanonicalDotsSources.SourceValue
    (CuSavingsRetainedResumeDotBinding.input (g.val[i]'(by rw [g.property];exact hi)))

theorem sourcePrefix_eq (B : Boundaries) (dot : AspisR1RetainedDots.Shared)
    {H : Type} (D : Q.D H) (v : Q.View) (p : Q.Prepared) (g : G) (hg : SourceTable g)
    (hash : H) (obs : Option (Q.Phase→Result Unit)) (geometry : Q.Geometry) (i : Usize) :
    sourcePrefix B (CuSavingsRetainedDotsBinding.newShared dot)
      (@AspisR1RetainedDots.prefix_new_dots.four_dots) D v p g hash obs geometry i =
    sourcePrefix B (CuSavingsRetainedDotsBinding.oldShared dot)
      (@AspisR1RetainedDots.old_dots.four_dots) D v p g hash obs geometry i := by
  unfold sourcePrefix
  apply (bind_eq_iff _ _ _).mpr
  intro u hu
  apply CuSavingsRetainedDotsInputs.query_equivalence dot (view v) i
    (CuSavingsRetainedResumeDotBinding.preparedTable g) ?_
    (fun q kernel=>do
      let authenticated←B.authenticate D v p hash obs geometry i u q
      match authenticated with
      | .Err error=>.ok (.Err error)
      | .Ok _=>do let dots←kernel ();B.fold D v p hash obs geometry i u q dots)
  intro j hj
  simpa only [CuSavingsRetainedResumeDotBinding.preparedTable,List.getElem_map,
    CuSavingsRetainedResumeDotBinding.toPrepared,CuSavingsRetainedSamplerInputs.input_fromInput] using hg j hj

#print axioms sourcePrefix_eq
end AspisR1.CuSavingsRetainedQueryPrefixBinding
