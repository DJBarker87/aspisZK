import RPz7_F3J_QueryLog
import RPz7_F3J_SemanticLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_QueryPairs
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation SourceDigestAddresses
abbrev RawState := Array U8 32#usize
abbrev Call := Slice (Slice U8) × RawState

/-- Successful individual source digest calls, with their actual carried
advance state. Association with the unrolled installed query body is separate. -/
inductive Pairs {Hash : Type} (D : aspis_core.Digest32 Hash) (hash : Hash) :
    Nat → RawState → List Call → Prop where
  | nil (state : RawState) : Pairs D hash 0 state []
  | cons {n : Nat} {state block next : RawState} {tail : List Call}
      (squeeze : D.digest hash (TranscriptStep.readParts state 1#u8)=ok block)
      (advance : D.digest hash (TranscriptStep.readParts state 2#u8)=ok next)
      (rest : Pairs D hash n next tail) :
      Pairs D hash (n+1) state ((TranscriptStep.readParts state 1#u8,block)::
        (TranscriptStep.readParts state 2#u8,next)::tail)

def observed (calls : List Call) : List (Bytes × State) :=
  calls.map (fun c => (flatten c.1,decodeState c.2))

theorem ordered {Hash : Type} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    {n : Nat} {state : RawState} {calls : List Call} (pairs : Pairs D hash n state calls) :
    observed calls=(F3J_QueryLog.issued SelectedTranscriptParams.params
      (fun a => H a.toBytes) n (decodeState state)).map (fun q => (q.1.toBytes,q.2)) := by
  induction pairs with
  | nil state => rfl
  | @cons n state block next tail squeeze advance rest ih =>
    let p := SelectedTranscriptParams.params
    have hb := backend _ ⟨hash,_,block,rfl,squeeze⟩
    have hn := backend _ ⟨hash,_,next,rfl,advance⟩
    change decodeState block=H (flatten _) at hb
    change decodeState next=H (flatten _) at hn
    rw [squeeze_address p] at hb
    rw [advance_address p] at hn
    simp only [observed,List.map_cons,F3J_QueryLog.issued]
    rw [squeeze_address p,advance_address p,← hb,← hn]
    exact congrArg (List.cons ((squeezeA p (decodeState state)).toBytes,decodeState block))
      (congrArg (List.cons ((advanceA p (decodeState state)).toBytes,decodeState next)) ih)

#print axioms ordered
end AspisR1.F3J_QueryPairs
end
