import RecordedBinaryExperimentBin
import BinDecoderInitialStarts

/-! Draft causal refinement. The gate is a mathematical specification, not
an executable parser. It uses only a witnessed past, not the current answer.
Causality alone deliberately imposes no frozen row payload grammar. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRowAwareCausalD1
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler (RunView)
attribute [local instance] Classical.propDecidable

abbrev Old := RecordedBinaryExperimentBin.dec

def Subtable (U T : Table Bytes State) : Prop :=
  ∀ a v, U a = some v → T a = some v

/-- The entire preceding row has been answered, and its start was recognised
in an earlier subtable. Recursing reaches the initial message at row zero.
The existential oracle supplies a consistent interpretation of cached bytes;
no answer to the proposed current query is inspected by this predicate. -/
def History (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (T : Table Bytes State) : Nat → Prop
  | 0 => pub.tag = 2 ∧ ∃ root word, pf 0 = .initial root word
  | n+1 => History D H pub pf T n ∧
      (∀ q ∈ (eval H ((LiteralByteProtocol.protocol D).chain H pub pf n).toProgram).1,
        T q.1 = some q.2) ∧
      ∃ a U, firstCell ((LiteralByteProtocol.protocol D).chain H pub pf n) = some a ∧
        Subtable U T ∧ Old a U ≠ none

def Gate (D : LiteralByteProtocol.Decoder) (a : Bytes) (T : Table Bytes State) : Prop :=
  ∃ H pub pf n, n < 33 ∧ History D H pub pf T n ∧
    firstCell ((LiteralByteProtocol.protocol D).chain H pub pf n) = some a

def decode (D : LiteralByteProtocol.Decoder) :=
  fun a T => if Gate D a T then Old a T else none

theorem decode_of_gate (D : LiteralByteProtocol.Decoder) (a : Bytes)
    (T : Table Bytes State) (h : Gate D a T) : decode D a T = Old a T := by
  exact if_pos h

theorem decode_some (D : LiteralByteProtocol.Decoder) (a : Bytes)
    (T : Table Bytes State) (own : BS Bytes State (List State))
    (pend : List (Bytes × Option State))
    (g : List State → List State → RawLiteralDecoderDensity.LiteralOutput) :
    decode D a T = some (own,pend,g) ↔
      Gate D a T ∧ Old a T = some (own,pend,g) := by
  unfold decode
  split <;> simp_all

/-- Retained starts preserve the complete background computation and output
function, so all follows (and every function of their recovered value) agree. -/
theorem retained_value (D : LiteralByteProtocol.Decoder) (a : Bytes)
    (T : Table Bytes State) (h : Gate D a T)
    (tr : List (Bytes × State))
    (consume : RawLiteralDecoderDensity.LiteralOutput → Option LiteralProtocol.Witness) :
    (decode D a T).bind (fun (own,pend,g) => (bfollow g tr own pend T).bind consume) =
    (Old a T).bind (fun (own,pend,g) => (bfollow g tr own pend T).bind consume) := by
  rw [decode_of_gate D a T h]

/-- Identical row density, with precisely the existing classifier budget. -/
theorem density (D : LiteralByteProtocol.Decoder) :
    ChainDensity3 (LiteralByteProtocol.protocol D) LiteralByteProtocol.rows (decode D) := by
  intro a T own pend g hd
  exact RawAdaptiveLiteralDecoder.density D RawFullPublicSelection.select
    LiteralTableWordChoiceBin.choose a T own pend g ((decode_some D a T own pend g).mp hd).2

#print axioms decode_of_gate
#print axioms decode_some
#print axioms retained_value
#print axioms density
end AspisR1.OraclePortRowAwareCausalD1
end
