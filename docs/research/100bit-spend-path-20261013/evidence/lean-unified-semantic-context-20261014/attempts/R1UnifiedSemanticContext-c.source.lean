import R1UnifiedSemanticRecovery
import R1IndexedMessage

/-! Recover the initial state, semantic records, and one canonically encoded
message from a state-frame absorb address and its preceding table. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedSemanticContext

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

structure Context (M : Type) where
  c1 : State
  records : List (Rec M)
  message : M

def parse (p : Params M Cv L) (pubBytes : Bytes) (a : Addr L)
    (T : Table (Addr L) State) : Option (Context M) :=
  (parseAbsorb a).bind fun (endpoint, label, data) =>
    (UnifiedSemanticRecovery.typed p pubBytes T 27 endpoint).bind fun (c1, rs) =>
      (IndexedMessage.read p rs.length label data).map fun m => ⟨c1, rs, m⟩

theorem parse_of_checks (p : Params M Cv L) (pubBytes : Bytes) (a : Addr L)
    (T : Table (Addr L) State) (endpoint : State) (label : Byte) (data : Bytes)
    (c1 : State) (rs : List (Rec M)) (message : M)
    (habs : parseAbsorb a = some (endpoint, label, data))
    (htyped : UnifiedSemanticRecovery.typed p pubBytes T 27 endpoint = some (c1, rs))
    (hread : IndexedMessage.read p rs.length label data = some message) :
    parse p pubBytes a T = some ⟨c1, rs, message⟩ := by
  simp [parse, habs, htyped, hread]

theorem parse_sound (p : Params M Cv L) (pubBytes : Bytes) (a : Addr L)
    (T : Table (Addr L) State) (ctx : Context M)
    (h : parse p pubBytes a T = some ctx) :
    ∃ endpoint label data,
      parseAbsorb a = some (endpoint, label, data) ∧
      UnifiedSemanticRecovery.typed p pubBytes T 27 endpoint =
        some (ctx.c1, ctx.records) ∧
      IndexedMessage.read p ctx.records.length label data = some ctx.message := by
  unfold parse at h
  cases habs : parseAbsorb a with
  | none => simp [habs] at h
  | some parsed =>
    rcases parsed with ⟨endpoint, label, data⟩
    simp only [habs, Option.bind_some] at h
    cases htyped : UnifiedSemanticRecovery.typed p pubBytes T 27 endpoint with
    | none => simp [htyped] at h
    | some recovered =>
      rcases recovered with ⟨c1, rs⟩
      simp only [htyped, Option.bind_some] at h
      cases hread : IndexedMessage.read p rs.length label data with
      | none => simp [hread] at h
      | some message =>
        simp only [hread, Option.map_some] at h
        have hctx : ({ c1 := c1, records := rs, message := message } : Context M) = ctx := by
          exact Option.some.inj h
        subst ctx
        exact ⟨endpoint, label, data, rfl, htyped, hread⟩

#print axioms parse_of_checks
#print axioms parse_sound

end AspisR1.UnifiedSemanticContext
end
