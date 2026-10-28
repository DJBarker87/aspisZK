import NCM_ViewAddress

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_LeafSelected
open Aeneas Aeneas.Std Result ControlFlow MultiproofConeRef NCE_OpeningCuts
open NCE_LeafCuts Port4B_LeafStep
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

def step {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (get : NCE_KeyReadCuts.Read) (reader : Reader) (request : Request) (post : Post)
    (kind : Usize) (batch : Nat) (s : Carrier) (keys : Array U64 16#usize) (cursor : Usize) :
    Result (ControlFlow LoopState LoopOut × Carrier × Array U64 16#usize) := do
  let got ← NCM_KeyView.read get reader s keys cursor batch
  let out ← NCM_Leaf.step D hash request post kind got.2.2.1 got.2.2.2.2 (Port4B_NativeLeaf.decodedIndex got.1) got.2.1
  ok (out.1,out.2,got.2.2.2.1)

/-- The same raw getter result feeds the same opening, syscall and post-hash
continuation. This is ONE active leaf iteration, including duplicate failure. -/
theorem observation {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State)
    (law : ∀ input, D.digest hash input = ok (MultiproofConePhysicalTransport.rawOracle H input))
    (get : NCE_KeyReadCuts.Read) (getCut : NCE_KeyReadCuts.NCE_Native_KeysRead get)
    (reader : Reader) (readerCut : NCE_Native_Opening reader)
    (request : Request) (post : Post) (leafCut : NCE_Native_Leaf request post)
    (kind : Usize) (batch : Nat) (s : Carrier) (keys : Array U64 16#usize) (cursor : Usize)
    (cb : cursor.val < 16) (kb : kind.val < 3) (room : s.scratch.n.val < 16)
    (q : Fin 22 → Fin 262144) (selected : Nat)
    (member : selected ∈ OraclePortSelectedDraft.batchPositions batch)
    (key : keys.val[cursor.val]! = MultiproofConeSortOrder.packed q batch kind.val selected)
    (size : s.proof.val.length = 57607) (parsed : OraclePortCompactDraft.Parsed)
    (wire : parsed.wire = MultiproofConeCanonical.bytesOf s.proof.val) :
    step D hash get reader request post kind batch s keys cursor =
      let input := OraclePortSelectedDraft.leaf parsed kind.val selected
      let afterRead := {s with log:=s.log++[(input,H input)]}
      let out := project s.scratch (Usize.wrapping_add cursor 1#usize)
        (MultiproofConeLeafContent.next s.scratch (MultiproofConeLeafFold.key q kind.val selected)
          (encodeState (H input)) room)
      ok (out,returnedCarrier afterRead out,keys) := by
  obtain ⟨view,source,len,opened⟩ := NCM_KeyView.observation get getCut reader readerCut s keys cursor cb q batch kind.val selected member key size
  have base : (NCE_KeyOpeningJoin.lo batch).val = (if batch=0 then 0 else 10) := by
    unfold NCE_KeyOpeningJoin.lo
    split <;> rfl
  have decoded := Port4B_KeyDecode.packed q batch kind.val selected member (NCE_KeyOpeningJoin.lo batch) base
  have position := MultiproofConeKeyAdapters.position_bounds batch selected member
  have address := NCM_ViewAddress.address s size parsed wire
    (Port4B_NativeLeaf.openingIndex (NCE_KeyOpeningJoin.lo batch) (MultiproofConeSortOrder.packed q batch kind.val selected))
    kind (by rw [decoded.2];exact position.2) view source
  rw [decoded.2] at address
  have index : Port4B_NativeLeaf.decodedIndex (MultiproofConeSortOrder.packed q batch kind.val selected) =
      MultiproofConeLeafFold.key q kind.val selected := by
    apply UScalar.eq_of_val_eq
    exact decoded.1
  simp only [step,opened,bind_tc_ok,index]
  rw [NCM_Leaf.observation D hash H law request post leafCut kind view s
    (MultiproofConeLeafFold.key q kind.val selected) (Usize.wrapping_add cursor 1#usize) kb len room]
  simp only [address,bind_tc_ok]

#print axioms observation
end AspisR1.NCM_LeafSelected
end
