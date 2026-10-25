import F3K_QueryChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_QueryValues
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation SourceDigestAddresses
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
abbrev RawState := F3J_QueryPairs.RawState

inductive Values {Hash : Type} (D : aspis_core.Digest32 Hash) (hash : Hash) :
    Nat → RawState → List RawState → List RawState → Prop where
  | nil (s : RawState) : Values D hash 0 s [] []
  | cons {n : Nat} {s b x : RawState} {bs xs : List RawState}
      (squeeze : D.digest hash (TranscriptStep.readParts s 1#u8)=ok b)
      (advance : D.digest hash (TranscriptStep.readParts s 2#u8)=ok x)
      (rest : Values D hash n x bs xs) :
      Values D hash (n+1) s (b::bs) (x::xs)

theorem lengths {Hash : Type} {D : aspis_core.Digest32 Hash} {hash : Hash}
    {n : Nat} {s : RawState} {bs xs : List RawState} (v : Values D hash n s bs xs) :
    bs.length=n ∧ xs.length=n := by
  induction v with
  | nil => exact ⟨rfl,rfl⟩
  | cons _ _ _ ih => simpa only [List.length_cons] using ⟨congrArg Nat.succ ih.1,congrArg Nat.succ ih.2⟩

theorem pairs {Hash : Type} {D : aspis_core.Digest32 Hash} {hash : Hash}
    {n : Nat} {s : RawState} {bs xs : List RawState} (v : Values D hash n s bs xs) :
    ∃ calls,F3J_QueryPairs.Pairs D hash n s calls := by
  induction v with
  | nil s => exact ⟨[],.nil s⟩
  | cons squeeze advance rest ih =>
    obtain ⟨calls,h⟩ := ih
    exact ⟨_,.cons squeeze advance h⟩

/-- Both lists retain every source output in chronological pair order. -/
theorem deterministic {Hash : Type} {D : aspis_core.Digest32 Hash} {hash : Hash}
    {n : Nat} {s : RawState} {bs xs : List RawState} (v : Values D hash n s bs xs)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H) :
    bs.map decodeState=(List.range n).map (fun k =>
      H ((FS2.Duplex.squeezeA SelectedTranscriptParams.params
        (QuerySampler.state SelectedTranscriptParams.params (fun a => H a.toBytes) (decodeState s) k)).toBytes)) ∧
    xs.map decodeState=(List.range n).map (fun k =>
      QuerySampler.state SelectedTranscriptParams.params (fun a => H a.toBytes) (decodeState s) (k+1)) := by
  induction v with
  | nil s => exact ⟨rfl,rfl⟩
  | @cons n s b x bs xs squeeze advance rest ih =>
    let p := SelectedTranscriptParams.params
    have hb := backend _ ⟨hash,_,b,rfl,squeeze⟩
    have hx := backend _ ⟨hash,_,x,rfl,advance⟩
    change decodeState b=H (flatten _) at hb
    change decodeState x=H (flatten _) at hx
    rw [squeeze_address p] at hb
    rw [advance_address p] at hx
    constructor
    · rw [QuerySampler.map_range_succ]
      change decodeState b :: bs.map decodeState =
        H ((FS2.Duplex.squeezeA p (decodeState s)).toBytes) ::
          (List.range n).map (fun k => H ((FS2.Duplex.squeezeA p
            (QuerySampler.state p (fun a => H a.toBytes) (decodeState s) (k+1))).toBytes))
      rw [← hb,ih.1]
      congr 1
      apply List.map_congr_left
      intro k hk
      rw [QuerySampler.state_succ',← hx]
    · rw [QuerySampler.map_range_succ]
      change decodeState x :: xs.map decodeState =
        H ((FS2.Duplex.advanceA p (decodeState s)).toBytes) ::
          (List.range n).map (fun k =>
            QuerySampler.state p (fun a => H a.toBytes) (decodeState s) ((k+1)+1))
      rw [← hx,ih.2]
      congr 1
      apply List.map_congr_left
      intro k hk
      rw [QuerySampler.state_succ' p _ (decodeState s) (k+1),← hx]

#print axioms lengths
#print axioms pairs
#print axioms deterministic
end AspisR1.F3K_QueryValues
end
