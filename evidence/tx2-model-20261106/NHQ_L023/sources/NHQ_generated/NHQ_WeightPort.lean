import NHQ_PacketPorts
set_option autoImplicit false
namespace NHQ_WeightPort
open Aeneas Aeneas.Std Result AspisR1
abbrev StageQ := AspisR1Stage2.Stage2Finish.K
abbrev NativeQ := NHE_DotBody.NQ

def native (q : StageQ) : NativeQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

theorem roundtrip (q : StageQ) : NHE_DotRead.stageQ (native q)=q := by
 cases q with
 | mk c0 c1 => cases c0;cases c1;rfl

def weights (ws : Slice StageQ) : Slice NativeQ := SAG_DotAdapter.mapSlice native ws

theorem width (ws : Slice StageQ) : (weights ws).val.length=ws.val.length := by
 simp only [weights,SAG_DotAdapter.mapSlice,List.length_map]

theorem same (ws : Slice StageQ) :
 SAG_DotAdapter.mapSlice NHE_DotRead.stageQ (weights ws)=ws := by
 apply Subtype.ext
 simp only [weights,SAG_DotAdapter.mapSlice,List.map_map]
 have identity : (fun q=>NHE_DotRead.stageQ (native q)) = id := funext roundtrip
 rw [identity,List.map_id]

#print axioms roundtrip
#print axioms width
#print axioms same
end NHQ_WeightPort
