import OraclePortCheckpointSlicesC5

/-! Save ten and resume twelve using decoded physical accumulator bytes.
Prepared query values/basis are recomputed from the same model data; proving
the frozen byte parser supplies that data remains a source/reader join. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCheckpointResumeC5
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortCheckpointAbiC5 OraclePortCheckpointSlicesC5
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OraclePortCheckpointStateC3.advance QueryAccumulator.run QueryAccumulator.run22

structure Context where
  state : State
  roots : Fin 2 → State
  semanticAlpha : Fin 10 → K
  coordinates : Fin 4 → K
  claim : E

def prepared (c : Context) (d : MatchingSupport.Data E) (rho : K)
    (q : Fin 22 → Fin 262144) : Prepared :=
  ⟨c.state,c.roots,d.gamma,d.kappa,(fun i => if i.val = 0 then d.alpha0 else d.alpha1),
    rho,q,c.semanticAlpha,c.coordinates,c.claim⟩

def decodeAccumulator (ck : Bytes) : Option (QueryAccumulator.State K E) := do
  if slice ck 0 16 = OraclePortPhysicalFrameDraft.magic ++ [2,10,1,0,0,0,0,0] then
    let rhs ← FoldedLeafCodec.decodeWide (slice ck 664 32)
    let power ← ExactLeafFieldCodec.decodeQM31 (slice ck 696 16)
    let weights ← decodeKs 64 (slice ck 712 1024)
    some ⟨weights,rhs,power,10⟩
  else none

theorem decode_written (H : Bytes → State) (stored pub : Bytes) (p : Prepared)
    (a : QueryAccumulator.State K E) (next : a.next = 10) :
    decodeAccumulator (encode H stored pub p a) = some a := by
  have header : slice (encode H stored pub p a) 0 16 =
      OraclePortPhysicalFrameDraft.magic ++ [2,10,1,0,0,0,0,0] :=
    field_at H stored pub p a 0 0 16 _ rfl rfl rfl (by decide)
  obtain ⟨rhs,power,weights⟩ := accumulator_decodes H stored pub p a
  simp only [decodeAccumulator,if_pos header,rhs,power,weights,Option.bind_eq_bind,Option.bind_some]
  cases a with
  | mk w r p n => simp only at next; subst n; rfl

structure Carrier where
  stored : Bytes
  checkpoint : Bytes

def model (d : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144) :
    OraclePortCheckpointStateC3.Prepared K E :=
  OraclePortCheckpointStateC3.fromData LiteralOpeningView.eK rho d q

/-- Saved fields come from the ten-step recurrence, never an external state. -/
def save (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144) : Carrier :=
  ⟨stored,encode H stored pub (prepared c d rho q)
    (OraclePortCheckpointStateC3.write (model d rho q)).accumulator⟩

/-- The retained proof slice is separate from the 1768-byte checkpoint. -/
theorem stored_retained (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144) :
    (save H stored pub c d rho q).stored = stored ∧
      (save H stored pub c d rho q).checkpoint.length = 1768 :=
  ⟨rfl,encode_length H stored pub _ _⟩

def HashBinding (H : Bytes → State) (pub : Bytes) (saved : Carrier) : Prop :=
  saved.checkpoint.length = 1768 ∧
  slice saved.checkpoint 16 32 = bytes (H saved.stored) ∧
  slice saved.checkpoint 48 32 = bytes (H pub) ∧
  saved.checkpoint.drop 1736 =
    bytes (H (OraclePortPhysicalFrameDraft.domain ++ saved.checkpoint.take 1736))

theorem save_hash_binding (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144) :
    HashBinding H pub (save H stored pub c d rho q) := by
  let p := prepared c d rho q
  let a := (OraclePortCheckpointStateC3.write (model d rho q)).accumulator
  have proofHash := field_at H stored pub p a 1 16 32 (bytes (H stored)) rfl rfl rfl (by decide)
  have publicHash := field_at H stored pub p a 2 48 32 (bytes (H pub)) rfl rfl rfl (by decide)
  obtain ⟨body,checksum⟩ := checksum_bound H stored pub p a
  refine ⟨encode_length H stored pub p a,proofHash,publicHash,?_⟩
  change (encode H stored pub p a).drop 1736 =
    bytes (H (OraclePortPhysicalFrameDraft.domain ++ (encode H stored pub p a).take 1736))
  rw [body,checksum]

/-- Hash checks bind the retained proof bytes. They are deliberately not
asserted to establish TX1 provenance; save supplies that provenance here. -/
def resume (H : Bytes → State) (pub : Bytes)
    (p : OraclePortCheckpointStateC3.Prepared K E) (saved : Carrier) :
    Option (QueryAccumulator.State K E) :=
  if HashBinding H pub saved then
    (decodeAccumulator saved.checkpoint).map (OraclePortCheckpointStateC3.advance p 12)
  else none

theorem physical_resume (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144) :
    resume H pub (model d rho q) (save H stored pub c d rho q) =
      some (QueryAccumulator.run22 LiteralOpeningView.eK rho
        (QueryResidualBridge.values d q) (QueryResidualBridge.basis q)) := by
  rw [resume,if_pos (save_hash_binding H stored pub c d rho q)]
  have decoded := decode_written H stored pub (prepared c d rho q)
    (OraclePortCheckpointStateC3.write (model d rho q)).accumulator
    (OraclePortCheckpointStateC3.saved_next _)
  change (decodeAccumulator (encode H stored pub _ _)).map _ = _
  rw [decoded,Option.map_some]
  have eq := (OraclePortCheckpointStateC3.resumed_state (model d rho q)).2
  trace_state
  exact congrArg some eq

/-- The model finish equation after physical resume is the existing R14 sum. -/
theorem physical_finish (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144)
    (a : QueryAccumulator.State K E)
    (resumed : resume H pub (model d rho q) (save H stored pub c d rho q) = some a) :
    (∑ l : Fin 64, d.f l * LiteralOpeningView.eK (a.weights l)) = a.rhs ↔
      HchecksAccumulator.ClosedSum LiteralOpeningView.eK d q rho := by
  rw [physical_resume,Option.some.injEq] at resumed
  subst a
  simp only [QueryAccumulator.run22_weights,QueryAccumulator.run22_rhs,
    HchecksAccumulator.ClosedSum]

#print axioms decode_written
#print axioms stored_retained
#print axioms save_hash_binding
#print axioms physical_resume
#print axioms physical_finish
end AspisR1.OraclePortCheckpointResumeC5
end
