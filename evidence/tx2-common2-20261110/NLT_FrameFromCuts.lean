import NLT_NativeOrder
import NLT_Select
set_option autoImplicit false
noncomputable section
namespace NLT_FrameFromCuts
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NLT_NativeInvocation NLT_SiteOrder
def resumeAt : (e : Event) → NLT_NativeWindows.Input e → Option NP6_StdModel.Reservation
 | .resume ..,r => some r
 | _,_ => none
def pendingAt : (e : Event) → NLT_NativeWindows.Input e → Option NP6_StdModel.Reservation
 | .pending ..,r => some r
 | _,_ => none
def finishAt : (e : Event) → NLT_NativeWindows.Input e →
 Option (NP6_StdModel.Reservation × NIW_AlignFinishComposed.Locations)
 | .finish ..,r => some r
 | _,_ => none
def resumeChoice {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 (r : Occurrence H d hash) := resumeAt r.entered r.input
def pendingChoice {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 (r : Occurrence H d hash) := pendingAt r.entered r.input
def finishChoice {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 (r : Occurrence H d hash) := finishAt r.entered r.input
/-- Defaults affect only sites never reached; they are not allocator events. -/
def unusedLocations : NIW_AlignFinishComposed.Locations := ⟨0,0,0,0,0,0,0,0,0⟩
def frame {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 (records : List (Occurrence H d hash)) : NLT_Interpreted.Uninstalled :=
 let last:=(NLT_Select.pick finishChoice records).getD (.Ok (),unusedLocations)
 ⟨(NLT_Select.pick resumeChoice records).getD (.Ok ()),
  (NLT_Select.pick pendingChoice records).getD (.Ok ()),last.1,last.2⟩
theorem resume_rank {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 (r : Occurrence H d hash) (x : NP6_StdModel.Reservation) (h : resumeChoice r=some x) :
 rank (actual r)=0 := by
 rcases r with ⟨e,input,detail⟩
 cases e <;> simp only [resumeChoice,resumeAt] at h <;> try contradiction
 exact NLT_NativeWindows.rank_window H d hash _ input

theorem pending_rank {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 (r : Occurrence H d hash) (x : NP6_StdModel.Reservation) (h : pendingChoice r=some x) :
 rank (actual r)=5 := by
 rcases r with ⟨e,input,detail⟩
 cases e <;> simp only [pendingChoice,pendingAt] at h <;> try contradiction
 exact NLT_NativeWindows.rank_window H d hash _ input

theorem finish_rank {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 (r : Occurrence H d hash) (x : NP6_StdModel.Reservation × NIW_AlignFinishComposed.Locations)
 (h : finishChoice r=some x) : rank (actual r)=8 := by
 rcases r with ⟨e,input,detail⟩
 cases e <;> simp only [finishChoice,finishAt] at h <;> try contradiction
 exact NLT_NativeWindows.rank_window H d hash _ input
/-- The global interpreter fields are OUTPUT projections of one ordered cut
trace. Their consistency is proved; no caller supplies it as a root clause. -/
theorem compatible {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 (records : List (Occurrence H d hash))
 (ordered : records.Pairwise (fun a b=>rank (actual a)<rank (actual b)))
 (r : Occurrence H d hash) (member : r∈records) :
 NLT_NativeWindows.Compatible (frame records) r.entered r.input := by
 have sr:=NLT_Select.unique (fun r : Occurrence H d hash=>rank (actual r)) resumeChoice 0
  resume_rank records ordered r member
 have sp:=NLT_Select.unique (fun r : Occurrence H d hash=>rank (actual r)) pendingChoice 5
  pending_rank records ordered r member
 have sf:=NLT_Select.unique (fun r : Occurrence H d hash=>rank (actual r)) finishChoice 8
  finish_rank records ordered r member
 rcases r with ⟨e,input,detail⟩
 cases e <;> try exact True.intro
 case resume ck proof pub reply =>
  have selected:=sr input rfl
  change input=(NLT_Select.pick resumeChoice records).getD (.Ok ())
  rw [selected]
  rfl
 case pending weights reply =>
  have selected:=sp input rfl
  change input=(NLT_Select.pick pendingChoice records).getD (.Ok ())
  rw [selected]
  rfl
 case finish v p a reply =>
  have selected:=sf input rfl
  change input.1=((NLT_Select.pick finishChoice records).getD (.Ok (),unusedLocations)).1 ∧
   input.2=((NLT_Select.pick finishChoice records).getD (.Ok (),unusedLocations)).2
  rw [selected]
  exact ⟨rfl,rfl⟩
set_option pp.proofs false
#print compatible
#print axioms resume_rank
#print axioms pending_rank
#print axioms finish_rank
#print axioms compatible
end NLT_FrameFromCuts
