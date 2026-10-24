import Port1_CanonicalJoin

/-! Physical source entry on arbitrary submitted bytes. Logical totalization
is never a gate in this entry. Only accepted-input transport uses admission. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port1_ByteDriver
open Aeneas Aeneas.Std Result VTop_Stages VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 Port1_StoredCarrier

/-- Same source cone as Port1_Driver.rust, before logical carrier construction. -/
def rust (adapter : AdapterRw.Ops) (impl : Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (s : Submission) :
    Program Bytes State Bool :=
  match Port1_Driver.asSlice s.publicBytes, Port1_Driver.asSlice s.stored with
  | some pub, some proof =>
    match Port1_Driver.decodeSemantic adapter pub with
    | .ok (some semantic) => Port1_Driver.stages impl D hash semantic pub proof
    | _ => .done false
  | _, _ => .done false

/-- A size consequence of the actual decoder/validator, retained as an S6
source port. It asserts no verifier success, log, output or model identity. -/
def PublicAdmission (adapter : AdapterRw.Ops) : Prop :=
  ∀ (pub : Slice U8) (semantic : Port1_Driver.Semantic),
    Port1_Driver.decodeSemantic adapter pub = .ok (some semantic) →
      75 + pub.val.length ≤ SelectedTranscriptParams.L

theorem slice_length (b : Bytes) (s : Slice U8) (h : Port1_Driver.asSlice b = some s) :
    s.val.length = b.length := by
  unfold Port1_Driver.asSlice at h
  split at h
  · cases h
    simp only [List.length_map]
  · cases h

theorem admitted (adapter : AdapterRw.Ops) (admission : PublicAdmission adapter)
    (impl : Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (s : Submission) (H : Bytes → State)
    (accepted : (eval H (rust adapter impl D hash s)).2 = true) :
    75 + s.publicBytes.length ≤ SelectedTranscriptParams.L := by
  cases pub : Port1_Driver.asSlice s.publicBytes with
  | none => simp only [rust,pub,eval,Bool.false_eq_true] at accepted
  | some publicBytes =>
    cases proof : Port1_Driver.asSlice s.stored with
    | none => simp only [rust,pub,proof,eval,Bool.false_eq_true] at accepted
    | some storedBytes =>
      cases decoded : Port1_Driver.decodeSemantic adapter publicBytes with
      | fail e => simp only [rust,pub,proof,decoded,eval,Bool.false_eq_true] at accepted
      | div => simp only [rust,pub,proof,decoded,eval,Bool.false_eq_true] at accepted
      | ok semantic =>
        cases semantic with
        | none => simp only [rust,pub,proof,decoded,eval,Bool.false_eq_true] at accepted
        | some value =>
          have h := admission publicBytes value decoded
          rw [slice_length _ _ pub] at h
          exact h

theorem canonical_eq (adapter : AdapterRw.Ops) (impl : Implementation)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : Submission) (bound : 75 + s.publicBytes.length ≤ SelectedTranscriptParams.L) :
    rust adapter impl D hash s = Port1_Driver.rust adapter impl D hash (input s) := by
  simp only [rust,Port1_Driver.rust,public_bytes s bound,input]

theorem accepted_transport (adapter : AdapterRw.Ops) (admission : PublicAdmission adapter)
    (impl : Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (s : Submission) (H : Bytes → State)
    (accepted : (eval H (rust adapter impl D hash s)).2 = true) :
    rust adapter impl D hash s = Port1_Driver.rust adapter impl D hash (input s) :=
  canonical_eq adapter impl D hash s (admitted adapter admission impl D hash s H accepted)

/-- Named body joins substitute the actual byte entry without changing what
it receives. The conclusion remains a source/model-dictionary substitution. -/
theorem substitute (adapter : AdapterRw.Ops) (admission : PublicAdmission adapter)
    (ops : Ops) (trusted : Port1_Library.TrustedStd ops)
    (source model : Implementation) (bodies : Port1_DriverSubstitution.BodyJoins source model)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : Submission) (H : Bytes → State)
    (accepted : (eval H (rust adapter (Port1_Library.implementation ops source) D hash s)).2 = true) :
    eval H (rust adapter (Port1_Library.implementation ops source) D hash s) =
      eval H (rust adapter (Port1_Library.implementation (Port1_Library.std ops) model) D hash s) := by
  have bound := admitted adapter admission _ D hash s H accepted
  rw [canonical_eq adapter _ D hash s bound] at accepted ⊢
  rw [canonical_eq adapter _ D hash s bound]
  exact Port1_DriverSubstitution.driver_substitute adapter _ _
    (Port1_DriverSubstitution.ports ops trusted source model bodies) D hash H (input s) accepted

#print axioms slice_length
#print axioms admitted
#print axioms canonical_eq
#print axioms accepted_transport
#print axioms substitute
end AspisR1.Port1_ByteDriver
end
