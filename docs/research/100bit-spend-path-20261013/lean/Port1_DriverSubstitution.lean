import Port1_Driver

/-! Library-premise removal and accepted substitution for the constructed
source driver. This does not identify the substituted driver with frozen2. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port1_DriverSubstitution
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open VTop_OracleStages OraclePortStoredExperimentC4 OraclePortFrozen2Join

structure BodyJoins (source model : Implementation) : Prop where
  shape : OperationJoin source model 3
  scan : OperationJoin source model 4
  batch : OperationJoin source model 5
  query : OperationJoin source model 6
  prepare : OperationJoin source model 7
  writer : OperationJoin source model 8
  flush : OperationJoin source model 9
  pending : OperationJoin source model 10
  geometry : OperationJoin source model 11
  initial : OperationJoin source model 12
  powers : OperationJoin source model 17
  reader : OperationJoin source model 18
  finish : OperationJoin source model 19

theorem body_operation (ops : Ops) (source model : Implementation) (id : Nat)
    (body : OperationJoin source model id) (nonlibrary : id ∉ libraryIds) :
    OperationJoin (Port1_Library.implementation ops source)
      (Port1_Library.implementation (Port1_Library.std ops) model) id := by
  intro A call operation H value accepted
  have notLibrary : operationId call ∉ libraryIds := by rw [operation]; exact nonlibrary
  simp only [Port1_Library.implementation, if_neg notLibrary] at accepted ⊢
  exact body call operation H value accepted

theorem ports (ops : Ops) (trusted : Port1_Library.TrustedStd ops)
    (source model : Implementation) (bodies : BodyJoins source model) :
    ConeJoins (Port1_Library.implementation ops source)
      (Port1_Library.implementation (Port1_Library.std ops) model) where
  shape := body_operation ops source model 3 bodies.shape (by decide)
  scan := body_operation ops source model 4 bodies.scan (by decide)
  batch := body_operation ops source model 5 bodies.batch (by decide)
  query := body_operation ops source model 6 bodies.query (by decide)
  prepare := body_operation ops source model 7 bodies.prepare (by decide)
  writer := body_operation ops source model 8 bodies.writer (by decide)
  flush := body_operation ops source model 9 bodies.flush (by decide)
  pending := body_operation ops source model 10 bodies.pending (by decide)
  geometry := body_operation ops source model 11 bodies.geometry (by decide)
  initial := body_operation ops source model 12 bodies.initial (by decide)
  powers := body_operation ops source model 17 bodies.powers (by decide)
  reader := body_operation ops source model 18 bodies.reader (by decide)
  finish := body_operation ops source model 19 bodies.finish (by decide)
  library := Port1_Library.library_join ops trusted source model

theorem driver_substitute (adapter : AdapterRw.Ops) (source model : Implementation)
    (joins : ConeJoins source model) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) :
    AcceptedVerifierJoin (Port1_Driver.rust adapter source D hash)
      (Port1_Driver.rust adapter model D hash) := by
  intro H i accepted
  cases pub : Port1_Driver.asSlice i.statement.pubBytes with
  | none => simp only [Port1_Driver.rust, pub, eval, Bool.false_eq_true] at accepted
  | some publicBytes =>
    cases proof : Port1_Driver.asSlice i.stored with
    | none => simp only [Port1_Driver.rust, pub, proof, eval, Bool.false_eq_true] at accepted
    | some storedBytes =>
      cases decoded : Port1_Driver.decodeSemantic adapter publicBytes with
      | fail e => simp only [Port1_Driver.rust, pub, proof, decoded, eval, Bool.false_eq_true] at accepted
      | div => simp only [Port1_Driver.rust, pub, proof, decoded, eval, Bool.false_eq_true] at accepted
      | ok semantic =>
        cases semantic with
        | none => simp only [Port1_Driver.rust, pub, proof, decoded, eval, Bool.false_eq_true] at accepted
        | some value =>
          simp only [Port1_Driver.rust, pub, proof, decoded] at accepted ⊢
          exact Port1_Driver.stages_substitute source model joins D hash value publicBytes storedBytes H accepted

#print axioms body_operation
#print axioms ports
#print axioms driver_substitute
end AspisR1.Port1_DriverSubstitution
end
