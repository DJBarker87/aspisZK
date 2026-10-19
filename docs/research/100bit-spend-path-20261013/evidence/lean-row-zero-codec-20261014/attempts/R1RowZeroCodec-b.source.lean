import R1PublicInitFrame
import R1IndexedMessage

/-! Connect the abstract row-zero frame to the indexed canonical codec. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RowZeroCodec

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem row0_absorb (p : Params M Cv L) (hD : 5 ≤ p.D) (m0 : M)
    (hl : p.lbl 0 = 160) (he : p.enc m0 = PublicInitFrame.emptyRecord)
    (s : State) :
    PublicInitFrame.row0 p hD s =
      absorbA p s (p.lbl 0) (p.enc m0) (p.encLen m0) := by
  simp only [PublicInitFrame.row0, hl, he]
  rfl

theorem decoded_empty (p : Params M Cv L) (m0 : M)
    (he : p.enc m0 = PublicInitFrame.emptyRecord) :
    p.dec PublicInitFrame.emptyRecord = some m0 := by
  simpa only [he] using p.decEnc m0

theorem indexed_empty (p : Params M Cv L) (m0 : M)
    (hl : p.lbl 0 = 160)
    (he : p.enc m0 = PublicInitFrame.emptyRecord) :
    IndexedMessage.read p 0 160 PublicInitFrame.emptyRecord = some m0 := by
  simpa only [hl, he] using IndexedMessage.read_encoded p 0 m0

#print axioms row0_absorb
#print axioms decoded_empty
#print axioms indexed_empty
end AspisR1.RowZeroCodec
end
