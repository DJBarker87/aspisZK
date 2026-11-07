import NLV_ExactFold
import NLV_Emit_guard
import NLV_EmissionSource
import NLV_CutFold
import NLV_InitialState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
/-- Complete SAME-argument source spine; ordering is proved, never an endpoint
hypothesis. Every inner Err and terminal outer fail/div keeps its exact log. -/
theorem initial_source (cfg : Configuration)
 (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (i : Input) (before : SdkC_Source.Log) :
 SdkC_Source.run h (fold cfg 20 ⟨i,.guard⟩) before =
 SdkC_Source.run h (GExp_FirstCode.code cfg.base cfg.boundaries cfg.std i.hashv
 i.digest i.publicValue i.publicBytes i.proof i.k) before := by
 rw [exact_source cfg h 20 ⟨i,.guard⟩ (Nat.le_refl 20)]
 change SdkC_Source.run h (suffix_guard cfg i) before=_
 rw [←NLV_EmitProof.eq_guard,NLV_EmissionSource.source]
/-- Parameterized physical fold. The proposed Cut producer remains OPEN;
this theorem is support only and never a CLOSED094 row root. -/
theorem from_cuts (cfg : Configuration) (i : Input) (frame : NLJ_Packets.Frame094)
 (observed : NGP_L181.Observation Out) (events : List NLV.Event) (last : NLV.State)
 (cuts : NLV.Invocation cfg i.hashv 20 (NLV.initial i frame)
  observed.result observed.attempted events last) :
 NGP_L181.NativeAssociation i.hashv
  (NGQ_Normalize.normalize (GExp_FirstCode.code cfg.base cfg.boundaries cfg.std i.hashv
    i.digest i.publicValue i.publicBytes i.proof i.k)) observed ∧
 last.external=(NLV.initial i frame).external ∧ last.core.input=i := by
 have source:=NHZ_DRIVER.frame (NLV.source_cuts cuts) []
 simp only [List.nil_append] at source
 change SdkC_Source.run i.hashv (fold cfg 20 ⟨i,.guard⟩) []=_ at source
 rw [initial_source] at source
 refine ⟨?_,NLV.external_frame_chain cuts,NLV.input_frame_chain cuts⟩
 unfold NGP_L181.NativeAssociation
 rw [NGQ_Normalize.run]
 exact source.symm
#print axioms initial_source
#print axioms from_cuts
set_option pp.proofs false
#print from_cuts
end AspisR1.NLV_Tree
end
