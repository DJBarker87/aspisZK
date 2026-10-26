import RPz7_T2R_Finish
import Par_Parameters
set_option autoImplicit false
noncomputable section
namespace AspisR1.TxS_Carriers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Raw public bytes and rounds contain no address-bound proof. -/
structure Prefix where
  publicBytes : Bytes
  tag : AspisV8R19.DuplexFrames.Byte
  rounds : List (RawCutTranscriptRun.ErasedMessage × LiteralTranscript.Challenge)

/-- Huge raw public carriers are mapped to the rejecting empty public encoding.
Every original typed prefix is preserved exactly (prefix_erase). -/
def toTyped (p : Prefix) : RawCutTranscriptRun.ErasedPrefix :=
  if h : 75+p.publicBytes.length≤SelectedTranscriptParams.L then
    ⟨⟨p.publicBytes,h,p.tag⟩,p.rounds⟩
  else ⟨⟨[],by norm_num [SelectedTranscriptParams.L],p.tag⟩,p.rounds⟩

def erase (p : RawCutTranscriptRun.ErasedPrefix) : Prefix :=
  ⟨p.statement.pubBytes,p.statement.tag,p.rounds⟩

theorem prefix_erase (p : RawCutTranscriptRun.ErasedPrefix) : toTyped (erase p)=p := by
  simp only [toTyped,erase,dif_pos p.statement.initFits]

def zeroData : MatchingSupport.Data LiteralTranscript.E :=
  ⟨0,0,0,0,0,0,0,0,0,0,0,0,0⟩

/-- Matching data is computed by the literal decoder, with a fixed rejected-case fallback. -/
def data (rs : LiteralAcceptanceTerminal.TranscriptRounds) : MatchingSupport.Data LiteralTranscript.E :=
  (LiteralMatchingData.read rs).getD zeroData

theorem data_of_read (rs : LiteralAcceptanceTerminal.TranscriptRounds)
    (d : MatchingSupport.Data LiteralTranscript.E) (read : LiteralMatchingData.read rs=some d) :
    data rs=d := by rw [data,read];rfl

/-- The input's matching data is no longer supplied by a model carrier. -/
structure Metadata where
  decoded : R0P.Public SemanticPublicWire.M31
  m31 : LiteralTranscript.Message
  queryBytes : List Nat
  state31 : State
  m32 : LiteralTranscript.Message
  rho : LiteralTranscript.E
  state32 : State

def source (m : Metadata) (rs : LiteralAcceptanceTerminal.TranscriptRounds) : R1FinalSoundness.SourceInputs :=
  ⟨m.decoded,data rs,m.m31,m.queryBytes,m.state31,m.m32,m.rho,m.state32⟩

def eraseInput (i : R1FinalSoundness.SourceInputs) : Metadata :=
  ⟨i.decoded,i.m31,i.queryBytes,i.state31,i.m32,i.rho,i.state32⟩

theorem source_of_read (rs : LiteralAcceptanceTerminal.TranscriptRounds)
    (i : R1FinalSoundness.SourceInputs) (read : LiteralMatchingData.read rs=some i.data) :
    source (eraseInput i) rs=i := by
  rw [source,data_of_read rs i.data read]
  rfl

/-- L151/L152 at the decoder-produced instance, never a law-bearing input. -/
theorem functional (m : Metadata) (rs : LiteralAcceptanceTerminal.TranscriptRounds)
    (x y : Fin 1024 → LiteralTranscript.E) (a : LiteralTranscript.E) :
    ((∀ j : Fin 6,(source m rs).data.F j (x+y)=(source m rs).data.F j x+(source m rs).data.F j y) ∧
      (source m rs).data.F0 (x+y)=(source m rs).data.F0 x+(source m rs).data.F0 y) ∧
    ((∀ j : Fin 6,(source m rs).data.F j (a • x)=a • (source m rs).data.F j x) ∧
      (source m rs).data.F0 (a • x)=a • (source m rs).data.F0 x) :=
  ⟨Par_Parameters.input_map_add _ x y,Par_Parameters.input_map_smul _ a x⟩

#print axioms prefix_erase
#print axioms data_of_read
#print axioms source_of_read
#print axioms functional
end AspisR1.TxS_Carriers
end
