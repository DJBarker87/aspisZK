import R1Z.PV_RunJoin_ScalarSource49
import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ScalarSuccess49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H) (self : host_transcript.Transcript H)
    (row : U8) (payload : Slice U8) (nonzero : Bool)
    (out : aspis_core.field.wide_exact.WideExact) (next : host_transcript.Transcript H)
    (h : @host_transcript.Transcript.scalar (types base) (selected base heap box ops) H D self row payload nonzero=ok (out,next)) :
    ∃ (block : Array U8 32#usize) (a : Raw),
      @host_transcript.Transcript.block H D self row payload=ok (block,next) ∧
      canonical a ∧ out=ProverRwDictionaryTower.fromW (source a) ∧
      a=PV_RunJoin_SamplerValue49.value base heap box ops block nonzero := by
  rw [PV_RunJoin_ScalarSource49.complete] at h
  unfold PV_RunJoin_ScalarSource49.retained at h
  obtain ⟨⟨block,tr⟩,hb,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  dsimp only [Aeneas.Std.uncurry] at h
  simp only [lift,bind_tc_ok] at h
  obtain ⟨unit,ht,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  have pair := Result.ok.inj h
  have hout := congrArg Prod.fst pair
  have htr := congrArg Prod.snd pair
  dsimp only at hout htr
  refine ⟨block,PV_RunJoin_SamplerValue49.value base heap box ops block nonzero,?_,
    (PV_RunJoin_SamplerValue49.spec base heap box ops block nonzero).2,hout.symm,rfl⟩
  rw [←htr]
  exact hb
#print axioms complete
end R1Z.PV_RunJoin_ScalarSuccess49
