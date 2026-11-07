import PV_THR2_Packet63To81Data
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Packet63To81
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Packet63To81Data
/-- Continue actual drop63 to actual13323 on the COMPLETE store. Only internal
cell inputs and named12950/13125 returned cases; arbitrary reply worlds and
all emitted moves persist. This is a continuation lemma, not original-entry
reachability. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b : Bool)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (argument captured hook : Data) (w : OWNER) (es : List E) (stack : List Config)
    (fresh : a < s.nextActivation)
    (argumentCell : s.cells ⟨a,24,[]⟩ = some argument)
    (closureCell : s.cells ⟨a,5,[]⟩ = some captured)
    (hookCell : s.cells ⟨a,13,[]⟩ = some hook) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    let q0 : PV_THR2_IntrinsicState.State OWNER E :=
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 63,loops := loops},parents,s⟩,w,es⟩,stack⟩
    let q1 := PV_THR2_Source361Full63.after B H q0
    let q2 := PV_THR2_Source361Chain64To70.after B q1
    let q3 := PV_THR2_Source361Full70.after B H q2
    let q4 := PV_THR2_Source361Chain71To76.after B q3
    let q5 := PV_THR2_Source361Aggregate76.after B q4
    let q6 := PV_THR2_Source361Chain77To81.after B q5
    PV_THR2_OwnInitExactReturnedCases.ReturnedAt B H q0
      (PV_THR2_F361.live.body.drop 63) PV_THR2_Source361PacketChildren.fn63 [.move (.local 24)] →
    PV_THR2_OwnInitExactReturnedCases.ReturnedAt B H q2
      (PV_THR2_F361.live.body.drop 70) PV_THR2_Source361PacketChildren.fn70 [.move (.local 26)] →
    ∃ counter metadata aggregate,
      let r63 := H (.child PV_THR2_Source361PacketChildren.fn63 s.nextActivation [argument]) w
      let t70 := moved70 s a argument counter captured
      let r70 := H (.child PV_THR2_Source361PacketChildren.fn70 t70.nextActivation [captured]) r63.world
      q6 = ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 81,loops := loops},parents,
        store81 s a argument counter captured metadata aggregate⟩,r70.world,(es ++ r63.events) ++ r70.events⟩,stack⟩ := by
  intro B q0 q1 q2 q3 q4 q5 q6 returned63 returned70
  let r63 := H (.child PV_THR2_Source361PacketChildren.fn63 s.nextActivation [argument]) w
  obtain ⟨counter,ret63,eq63⟩ := PV_THR2_PacketChild63Store.after C b H s a parents loops argument w es stack argumentCell returned63
  change q1 = ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 64,loops := loops},parents,
    store64 s a argument counter⟩,r63.world,es ++ r63.events⟩,stack⟩ at eq63
  have n0 : a ≠ s.nextActivation := Nat.ne_of_lt fresh
  have n1 : a ≠ s.nextActivation+1 := by omega
  have captured64 : (store64 s a argument counter).cells ⟨a,5,[]⟩ = some captured := by
    simpa [store64,moved63,PV_THR2_StaticReply.returnedStore,PV_THR2_StaticCall.issued,
      PV_STX2_Native.arguments,write,n0] using closureCell
  have eq70 := PV_THR2_PacketMetadata64Store.after C b (store64 s a argument counter) a parents loops
    r63.world (es ++ r63.events) stack captured captured64
  have q2eq : q2 = ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 70,loops := loops},parents,
    store70 s a argument counter captured⟩,r63.world,es ++ r63.events⟩,stack⟩ := by
    dsimp only [q2]; rw [eq63]; exact eq70
  have captured70 : (store70 s a argument counter captured).cells ⟨a,26,[]⟩ = some captured := by
    simp [store70,PV_THR2_Spawn361MetadataMove64Reached.prepared,write]
  rw [q2eq] at returned70
  obtain ⟨metadata,ret70,eq71⟩ := PV_THR2_PacketChild70Store.after C b H (store70 s a argument counter captured)
    a parents loops captured r63.world (es ++ r63.events) stack captured70 returned70
  let r70 := H (.child PV_THR2_Source361PacketChildren.fn70 (moved70 s a argument counter captured).nextActivation [captured]) r63.world
  have q3eq : q3 = ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 71,loops := loops},parents,
    store71 s a argument counter captured metadata⟩,r70.world,(es ++ r63.events) ++ r70.events⟩,stack⟩ := by
    dsimp only [q3]; rw [q2eq]; exact eq71
  have q4eq : q4 = ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 76,loops := loops},parents,
    store76 s a argument counter captured metadata⟩,r70.world,(es ++ r63.events) ++ r70.events⟩,stack⟩ := by
    dsimp only [q4]; rw [q3eq]
    exact PV_THR2_PacketMetadata71Store.after C b _ a parents loops _ _ stack
  have meta76 : (store76 s a argument counter captured metadata).cells ⟨a,25,[]⟩ = some metadata := by
    simp [store76,store71,PV_THR2_Spawn361MetadataStorage71Reached.prepared,PV_THR2_StaticReply.returnedStore,write]
  have hook76 : (store76 s a argument counter captured metadata).cells ⟨a,13,[]⟩ = some hook := by
    simpa [store76,store71,moved70,store70,store64,moved63,
      PV_THR2_Spawn361MetadataStorage71Reached.prepared,PV_THR2_Spawn361MetadataMove64Reached.prepared,
      PV_THR2_StaticReply.returnedStore,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write,n0,n1] using hookCell
  have count76 : (store76 s a argument counter captured metadata).cells ⟨a,23,[]⟩ = some counter := by
    simp [store76,store71,moved70,store70,store64,
      PV_THR2_Spawn361MetadataStorage71Reached.prepared,PV_THR2_Spawn361MetadataMove64Reached.prepared,
      PV_THR2_StaticReply.returnedStore,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write,n0,n1]
  obtain ⟨aggregate,eq77⟩ := PV_THR2_PacketMetadata76Store.after C b (store76 s a argument counter captured metadata)
    a parents loops metadata hook counter r70.world ((es ++ r63.events) ++ r70.events) stack meta76 hook76 count76
  have q5eq : q5 = ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 77,loops := loops},parents,
    store77 s a argument counter captured metadata aggregate⟩,r70.world,(es ++ r63.events) ++ r70.events⟩,stack⟩ := by
    dsimp only [q5]; rw [q4eq]; exact eq77
  refine ⟨counter,metadata,aggregate,?_⟩
  dsimp only [q6]; rw [q5eq]
  exact PV_THR2_PacketMetadata77Store.after C b _ a parents loops _ _ stack
#print axioms after
end PV_THR2_Packet63To81
