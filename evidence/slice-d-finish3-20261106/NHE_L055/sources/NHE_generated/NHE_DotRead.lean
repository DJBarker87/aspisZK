import NHE_PublicDot
set_option autoImplicit false
namespace NHE_DotRead
open Aeneas Aeneas.Std Result AspisR1
abbrev NE := FIo_Install.NE
abbrev NQ := NHE_CheckedScalar.NQ

def finishE (x : NE) := SAG_DotAdapter.toFinishE (FIo_Install.fromE x)
def stageQ (x : NQ) : AspisR1Stage2.Stage2Finish.K := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def finishQ (x : NQ) := SAG_DotAdapter.toFinishQ (stageQ x)

theorem map_comp {A B C : Type} (f : A → B) (g : B → C) (r : Result A) :
 FIo_FieldBridge.map g (FIo_FieldBridge.map f r)=FIo_FieldBridge.map (fun a=>g (f a)) r := by cases r <;> rfl

theorem field (bytes : Slice U8) (i : Usize) (small : i.val<64) :
 FIo_FieldBridge.map finishE (FIo_Native.weights.field bytes i)=AspisR1CurrentWide.Proof.finishField bytes i := by
 have h := congrArg (FIo_FieldBridge.map SAG_DotAdapter.toFinishE) (NHE_FieldPort.adopted bytes i small)
 rw [map_comp] at h
 unfold FIn_Primitives.field at h
 simp only [FIo_FieldBridge.map_bind,FIo_FieldBridge.map_ok,SAG_DotAdapter.roundtrip_finishE,FIn_ExtractInstall.bind_ok] at h
 exact h

theorem weight (weights : Slice NQ) (j : Usize) :
 FIo_FieldBridge.map finishQ (Slice.index_usize weights j)=
 Slice.index_usize (SAG_DotAdapter.mapSlice finishQ weights) j := by
 simp only [Slice.index_usize,Slice.getElem?_Usize_eq,SAG_DotAdapter.mapSlice,List.getElem?_map]
 cases h : weights.val[j.val]? <;> rfl

#print axioms map_comp
#print axioms field
#print axioms weight
end NHE_DotRead
