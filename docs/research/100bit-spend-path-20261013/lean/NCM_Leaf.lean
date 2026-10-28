import NCE_LeafCuts

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_Leaf
open Aeneas Aeneas.Std Result ControlFlow MultiproofConeRef NCE_OpeningCuts
open NCE_LeafCuts Port4B_LeafStep
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

def projected (raw : CheckpointBytes5Effect.Log) : NCE_FirstFailure.Log :=
  raw.map (fun e => (flatten e.1,decodeState e.2))

/-- ONE actual request followed by its post-hash continuation. The syscall
reply and raw chronological request list are consumed without recomputation. -/
def step {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (request : Request) (post : Post) (kind : Usize) (view : Slice U8)
    (s : Carrier) (index : U32) (pos : Usize) : Result (ControlFlow LoopState LoopOut × Carrier) := do
  let got ← CheckpointBytes5Effect.run D hash (request kind view) []
  post {s with log:=s.log++projected got.2} index got.1 pos

/-- SAME raw reply feeds duplicate/new/error continuation; rejection retains
its leaf request and the old log. No successful leaf premise is introduced. -/
theorem observation {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State)
    (law : ∀ input, D.digest hash input = ok (MultiproofConePhysicalTransport.rawOracle H input))
    (request : Request) (post : Post) (cut : NCE_Native_Leaf request post)
    (kind : Usize) (view : Slice U8) (s : Carrier) (index : U32) (pos : Usize)
    (kb : kind.val < 3) (size : view.val.length = 832) (room : s.scratch.n.val < 16) :
    step D hash request post kind view s index pos =
      let input := flatten (Port4B_LeafCode.input kind view)
      let afterRead := {s with log:=s.log++[(input,H input)]}
      let out := project s.scratch pos (MultiproofConeLeafContent.next s.scratch index (encodeState (H input)) room)
      ok (out,returnedCarrier afterRead out) := by
  simp only [step,NCE_LeafCuts.request_observation request post cut D hash H law kind view [] kb size,
    List.nil_append,bind_tc_ok,projected,List.map_cons,List.map_nil,state_roundtrip]
  exact NCE_LeafCuts.post_association request post cut {s with log:=s.log++[(flatten (Port4B_LeafCode.input kind view),H (flatten (Port4B_LeafCode.input kind view)))]} index _ pos room

#print axioms observation
end AspisR1.NCM_Leaf
end
