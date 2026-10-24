import S1SemanticFinishRootsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.S1SemanticRootCopy

/-- Rust result unwrap's successful value and panic rejection, without an
assumed successful conversion. Accepted-only use; native panic formatting and
runtime abort traces are separate standard/runtime correspondence gates. -/
def unwrapRoot (r : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError) :
    Result (Array U8 32#usize) :=
  match r with | .Ok root => ok root | .Err _ => fail .panic

def install (B : FinishModel.Boundaries) : FinishModel.Boundaries := {B with unwrapRoot:=unwrapRoot}

/-- Both semantic roots come from the SAME successful full finish. The second
is exactly every byte of its reached row-2 payload, with no root/length/copy
success premise. Other semantic children remain explicit in R and B. -/
theorem finish_roots (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (out : r1_semantic.Verified H)
    (success : FinishModel.finish R (install B) D pub pre before challenges none=ok (.Ok out)) :
    ∃ (payload : Slice U8) (root2 : Array U8 32#usize),
      FinishModel.payload pre 2#u8=ok (.Ok payload) ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload=ok (.Ok root2) ∧
      root2.val=payload.val ∧ out.roots=Array.make 2#usize [pre.c1_root,root2] := by
  obtain ⟨payload,copied,root2,hpayload,hcopy,hunwrap,hroots⟩ :=
    S1SemanticFinishRoots.finish_root_calls R (install B) D pub pre before challenges none out success
  change unwrapRoot copied=ok root2 at hunwrap
  cases copied with
  | Err error => cases hunwrap
  | Ok value =>
    have same : value=root2 := Result.ok.inj hunwrap
    subst value
    obtain ⟨r,run,fields⟩ := WP.spec_imp_exists
      (core.array.TryFromArrayCopySlice.try_from.step 32#usize core.marker.CopyU8 payload)
    have resultEq := Result.ok.inj (run.symm.trans hcopy)
    subst r
    exact ⟨payload,root2,hpayload,hcopy,fields.1,hroots⟩

#print axioms unwrapRoot
#print axioms finish_roots
end AspisR1PublicPreparation.S1SemanticRootCopy
