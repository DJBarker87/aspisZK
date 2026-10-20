import RawSourceGlobalOracleInitial

/-! Conditional tx1 log assembly. Inventory coverage is deliberately a named
obligation: no whole-tx1 execution trace is emitted by the retained extraction. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.Tx1DigestLog
open Aeneas Aeneas.Std Result AspisR1
open FS2.Duplex AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.DuplexFrames
open SourceDigestAddresses SourceDigestLog SourceGlobalOracleInitial

/-- A pair has a successful call witness in the actual extracted Digest32 API. -/
def ActualPair {Hash : Type} (D : aspis_core.Digest32 Hash) (q : Bytes × State) : Prop :=
  ∃ (hash : Hash) (input : Slice (Slice U8)) (output : TranscriptStep.Bytes32),
    q = (flatten input, decodeState output) ∧ D.digest hash input = ok output

/-- Named ROM/backend premise, including independence of part segmentation and
of the retained backend value. This is not a theorem about arbitrary Digest32. -/
def ByteOracleBackend {Hash : Type} (D : aspis_core.Digest32 Hash)
    (Hbytes : Bytes → State) : Prop :=
  ∀ q, ActualPair D q → q.2 = Hbytes q.1

/-- Rows 25–32 and the non-sampler calls (commitment authentication and the
three checkpoint hashes included) must be supplied separately. Repeated calls
are retained; this is not a first-read count or an ordered execution trace. -/
def log {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pub : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : TranscriptStep.Bytes32} {before : r1_wire.SemanticTranscript Hash}
    {pre : r1_wire.Prefix} (init : PublicInitCall D pub root before)
    (cs : List (SourceFull25.Call D pre))
    (samplerRows25To32 otherTx1Calls : List (Bytes × State)) : List (Bytes × State) :=
  initPair init :: (sourceLog cs ++ samplerRows25To32 ++ otherTx1Calls)

/-- Coverage must be derived from an execution extraction; source call witnesses
alone cannot establish that all reached calls have been listed. -/
def Tx1InventoryComplete (reached : Bytes × State → Prop)
    (tr : List (Bytes × State)) : Prop := ∀ q, reached q → q ∈ tr

def SamplerRows25To32Logged (rows : List (Bytes × State))
    (reachedSamplerSuffix : Bytes × State → Prop) : Prop :=
  ∀ q, reachedSamplerSuffix q → q ∈ rows

/-- Deferred tx2 execution embedding, at the same byte-oracle carrier. -/
def Tx2EmbeddingObligation (reachedTx2 : Bytes × State → Prop)
    (tr2 : List (Bytes × State)) : Prop := ∀ q, reachedTx2 q → q ∈ tr2

/-- Deferred cross-transaction obligation. Separate per-transaction oracles
are insufficient: both logs must agree with this SAME Hbytes. -/
def CrossTransactionConsistency (Hbytes : Bytes → State)
    (tr1 tr2 : List (Bytes × State)) : Prop :=
  ∀ q ∈ tr1 ++ tr2, q.2 = Hbytes q.1

theorem prefix_contained {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pub : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : TranscriptStep.Bytes32} {before : r1_wire.SemanticTranscript Hash}
    {pre : r1_wire.Prefix} (init : PublicInitCall D pub root before)
    (cs : List (SourceFull25.Call D pre)) (suffix rest : List (Bytes × State)) :
    initPair init :: sourceLog cs ⊆ log init cs suffix rest := by
  intro q hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ hq))

theorem log_actual {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pub : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : TranscriptStep.Bytes32} {before : r1_wire.SemanticTranscript Hash}
    {pre : r1_wire.Prefix} (init : PublicInitCall D pub root before)
    (cs : List (SourceFull25.Call D pre)) (suffix rest : List (Bytes × State))
    (hsuffix : ∀ q ∈ suffix, ActualPair D q)
    (hrest : ∀ q ∈ rest, ActualPair D q) :
    ∀ q ∈ log init cs suffix rest, ActualPair D q := by
  intro q hq
  simp only [log, List.mem_cons, List.mem_append] at hq
  rcases hq with rfl | ((hq | hq) | hq)
  · exact ⟨before.hash, _, init.state, rfl, init.digest⟩
  · obtain ⟨c, hc, hcall⟩ := List.mem_flatMap.mp hq
    obtain ⟨input, output, heq, hd⟩ := callLog_actual c q hcall
    exact ⟨c.before.hash, input, output, heq, hd⟩
  · exact hsuffix q hq
  · exact hrest q hq

theorem log_consistent {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pub : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : TranscriptStep.Bytes32} {before : r1_wire.SemanticTranscript Hash}
    {pre : r1_wire.Prefix} (init : PublicInitCall D pub root before)
    (cs : List (SourceFull25.Call D pre)) (suffix rest : List (Bytes × State))
    (hsuffix : ∀ q ∈ suffix, ActualPair D q)
    (hrest : ∀ q ∈ rest, ActualPair D q)
    (Hbytes : Bytes → State) (hbackend : ByteOracleBackend D Hbytes) :
    ∀ q ∈ log init cs suffix rest, q.2 = Hbytes q.1 := by
  intro q hq
  exact hbackend q (log_actual init cs suffix rest hsuffix hrest q hq)

theorem every_reached_call {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pub : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : TranscriptStep.Bytes32} {before : r1_wire.SemanticTranscript Hash}
    {pre : r1_wire.Prefix} (init : PublicInitCall D pub root before)
    (cs : List (SourceFull25.Call D pre)) (suffix rest : List (Bytes × State))
    (hsuffix : ∀ q ∈ suffix, ActualPair D q)
    (hrest : ∀ q ∈ rest, ActualPair D q)
    (Hbytes : Bytes → State) (hbackend : ByteOracleBackend D Hbytes)
    (reached : Bytes × State → Prop)
    (hinventory : Tx1InventoryComplete reached (log init cs suffix rest)) :
    ∀ q, reached q → q ∈ log init cs suffix rest ∧ q.2 = Hbytes q.1 := by
  intro q hq
  exact ⟨hinventory q hq,
    log_consistent init cs suffix rest hsuffix hrest Hbytes hbackend q (hinventory q hq)⟩

/-- A local pairwise coherence fact follows; it does not prove log ordering,
first-read budgets, memoized sampling laws or the missing inventory. -/
theorem same_address_same_output (Hbytes : Bytes → State)
    (tr : List (Bytes × State)) (hcons : ∀ q ∈ tr, q.2 = Hbytes q.1)
    (q r : Bytes × State) (hq : q ∈ tr) (hr : r ∈ tr) (ha : q.1 = r.1) :
    q.2 = r.2 := by rw [hcons q hq, hcons r hr, ha]

#print axioms prefix_contained
#print axioms log_actual
#print axioms log_consistent
#print axioms every_reached_call
#print axioms same_address_same_output
end AspisR1PublicPreparation.Tx1DigestLog
end
