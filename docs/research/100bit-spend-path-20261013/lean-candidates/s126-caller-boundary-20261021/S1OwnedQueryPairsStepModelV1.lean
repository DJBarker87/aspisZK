import S1OwnedQueryPairsFunsV1
import S1OwnedQueryBlockFixedModelV1
set_option autoImplicit false
namespace AspisS1OwnedQueryPairs.Model
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge
abbrev Block := Array U8 32#usize
abbrev Blocks := Array Block 8#usize

def project (s : OwnedScan) : Query31ExplicitScanBody.CurrentScan :=
  {accepted:=s.accepted,accepted_len:=s.accepted_len,draws:=s.draws}
def qState (s : OwnedScan) := Query31ExplicitScanBody.q22StateOf (project s)
def Valid (s : OwnedScan) : Prop := s.accepted_len.val≤22 ∧ s.draws.val≤64

def atBlock (a : Blocks) (i : Usize) (bound : i.val<8) : Block :=
  a.val[i.val]'(by have := a.property;scalar_tac)

theorem atBlock_call (a : Blocks) (i : Usize) (bound : i.val<8) :
    Array.index_usize a i=ok (atBlock a i bound) :=
  AspisS1QueryArrayOperations.index_total a i (by scalar_tac)

/-- TOTAL exact emitted owned driver step, including its selected advance and
complete returned scanner state. The fixed block call supplies all child
success/range/model facts; none is a separate caller premise. -/
theorem step_model (s : OwnedScan) (state : Block) (k : Usize)
    (blocks advances : Blocks) (bound : k.val<8) (valid : Valid s) :
    ∃ (after : OwnedScan) (next : Block) (stop : Bool),
      pairs_step s state k blocks advances=ok (after,next,stop) ∧ Valid after ∧
      AspisV8R19.Q22WordScan.scan (qState s)
        (AspisV8R19.SamplerWords.words 18 (decodeState (atBlock blocks k bound)))=
        (qState after,stop) ∧
      next=(if stop then atBlock advances k bound else state) := by
  obtain ⟨sf,stop,called,model,validFinal⟩ :=
    AspisS1OwnedQueryBlock.Meaning.block_fixed_model (project s) (atBlock blocks k bound)
      valid.1 valid.2
  dsimp only [project] at called
  let after : OwnedScan := {accepted:=sf.accepted,accepted_len:=sf.accepted_len,draws:=sf.draws}
  have validAfter : Valid after := ⟨validFinal.1,validFinal.2.1⟩
  have stateAfter : qState after=Query31ExplicitScanBody.q22StateOf sf := rfl
  have modelAfter : AspisV8R19.Q22WordScan.scan (qState s)
      (AspisV8R19.SamplerWords.words 18 (decodeState (atBlock blocks k bound)))=
      (qState after,stop) := by rw [stateAfter];exact model
  cases stop with
  | true =>
    refine ⟨after,atBlock advances k bound,true,?_,validAfter,modelAfter,rfl⟩
    unfold pairs_step
    rw [atBlock_call blocks k bound]
    simp only [bind_tc_ok]
    rw [called]
    simp only [AspisS1OwnedQueryBlock.Meaning.pack,bind_tc_ok,if_true]
    rw [atBlock_call advances k bound]
    rfl
  | false =>
    refine ⟨after,state,false,?_,validAfter,modelAfter,rfl⟩
    unfold pairs_step
    rw [atBlock_call blocks k bound]
    simp only [bind_tc_ok]
    rw [called]
    rfl

#print axioms atBlock_call
#print axioms step_model
end AspisS1OwnedQueryPairs.Model
