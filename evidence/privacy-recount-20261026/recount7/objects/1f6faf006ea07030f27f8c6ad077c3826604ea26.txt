import R1Z.PV_RunJoin_LaneLeaf31
import R1Z.PV_RunJoin_LaneNative31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LaneRootField31
open Aeneas Aeneas.Std Result R0Z.WriterRefine
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_Src_ExternalReference.dictionary
variable {K : Type} [Field K] [CharP K 2147483647]
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation

def meaning (x : PV_RunJoin_Outer30.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1) : R0P.Digest K :=
  let input := PV_RunJoin_LaneABI31.fromOuter x
  PV_RunJoin_LaneField31.fieldFold
    (fun l => digK (PV_RunJoin_LaneDenotation31.sibling input l))
    (PV_RunJoin_LaneDenotation31.reverse input) (List.range 20)
    (R0P.nodeCompress (digK x.pair_leaf.first_commitment) (digK x.pair_leaf.second_commitment))

theorem successful_root
    (x : PV_RunJoin_Outer30.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1)
    (root : Array U32 8#usize) (h : PV_RunJoin_LaneABI31.call x = ok (.Ok root))
    (siblings : ∀ l, l<20 → Canon8 x.membership.siblings.val[l]!) :
    Canon8 root ∧ digK (K := K) root = meaning x := by
  obtain ⟨d,hleaf,hfold⟩ := PV_RunJoin_LaneNative31.successful_root x root h
  have raw := PV_RunJoin_LaneLeaf31.returned _ d hleaf
  have canonical := PV_RunJoin_PairChecks29.leaf_canonical _ d raw
  have parent := PV_RunJoin_LaneLeaf31.parent _ d raw
  obtain ⟨d',hd,hcanon,hm⟩ := PV_RunJoin_LaneField31.parent_source (K := K) _ _ canonical.2
  have he : d=d' := Result.ok.inj (parent.symm.trans hd)
  subst d'
  obtain ⟨out,hout,hco,hlift⟩ := PV_RunJoin_LaneField31.fold_source (K := K)
    (PV_RunJoin_LaneDenotation31.sibling (PV_RunJoin_LaneABI31.fromOuter x))
    (PV_RunJoin_LaneDenotation31.reverse (PV_RunJoin_LaneABI31.fromOuter x))
    (List.range 20) d hcanon (fun l hl => siblings l (List.mem_range.mp hl))
  have he : out=root := Result.ok.inj (hout.symm.trans hfold)
  subst out
  refine ⟨hco,?_⟩
  rw [hm] at hlift
  exact hlift
#print axioms successful_root
end R1Z.PV_RunJoin_LaneRootField31
