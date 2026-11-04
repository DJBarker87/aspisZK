import Lean
import NFY_Part021
import NFY_Part035
import NFY_Part020
import NFY_Part036
import NFY_Part023

-- BEGIN copied JFt_Digest04: lean/JFt_Digest04.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest04
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [560027647#u32,109760138#u32,2064904093#u32,345398497#u32,1214731266#u32,366495038#u32,459312327#u32,480913462#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest04.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest04.window
    NFY_JFu_PublicDigest04.length NFY_JFu_PublicDigest04.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest04.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest04.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 400 32 (by decide)=NFY_JFu_PublicDigest04.window := by
  apply Subtype.ext
  exact NFY_JFu_PublicDigest04.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 400 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest04
-- END copied JFt_Digest04
-- BEGIN copied JFt_Digest05: lean/JFt_Digest05.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest05
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1603344092#u32,1242405009#u32,1153352827#u32,393697509#u32,714169239#u32,2094351560#u32,55834509#u32,664305674#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest05.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest05.window
    NFY_JFu_PublicDigest05.length NFY_JFu_PublicDigest05.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest05.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest05.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 432 32 (by decide)=NFY_JFu_PublicDigest05.window := by
  apply Subtype.ext
  exact NFY_JFu_PublicDigest05.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 432 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest05
-- END copied JFt_Digest05
-- BEGIN copied JFt_Digest06: lean/JFt_Digest06.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest06
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,1855504616#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest06.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest06.window
    NFY_JFu_PublicDigest06.length NFY_JFu_PublicDigest06.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest06.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest06.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 464 32 (by decide)=NFY_JFu_PublicDigest06.window := by
  apply Subtype.ext
  exact NFY_JFu_PublicDigest06.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 464 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest06
-- END copied JFt_Digest06
-- BEGIN copied JFt_Digest07: lean/JFt_Digest07.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest07
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,561084592#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest07.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest07.window
    NFY_JFu_PublicDigest07.length NFY_JFu_PublicDigest07.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest07.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest07.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 496 32 (by decide)=NFY_JFu_PublicDigest07.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest07.window]
  exact NFY_JFu_PublicDigest07.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 496 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest07
-- END copied JFt_Digest07
-- BEGIN copied JFt_Digest08: lean/JFt_Digest08.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest08
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,745931587#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest08.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest08.window
    NFY_JFu_PublicDigest08.length NFY_JFu_PublicDigest08.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest08.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest08.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 528 32 (by decide)=NFY_JFu_PublicDigest08.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest08.window]
  exact NFY_JFu_PublicDigest08.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 528 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest08
-- END copied JFt_Digest08
-- BEGIN copied JFt_Digest09: lean/JFt_Digest09.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest09
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,711700631#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest09.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest09.window
    NFY_JFu_PublicDigest09.length NFY_JFu_PublicDigest09.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest09.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest09.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 560 32 (by decide)=NFY_JFu_PublicDigest09.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest09.window]
  exact NFY_JFu_PublicDigest09.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 560 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest09
-- END copied JFt_Digest09
-- BEGIN copied JFt_Digest10: lean/JFt_Digest10.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest10
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,553704718#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest10.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest10.window
    NFY_JFu_PublicDigest10.length NFY_JFu_PublicDigest10.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest10.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest10.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 592 32 (by decide)=NFY_JFu_PublicDigest10.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest10.window]
  exact NFY_JFu_PublicDigest10.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 592 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest10
-- END copied JFt_Digest10
-- BEGIN copied JFt_Digest11: lean/JFt_Digest11.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest11
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,1653526885#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest11.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest11.window
    NFY_JFu_PublicDigest11.length NFY_JFu_PublicDigest11.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest11.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest11.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 624 32 (by decide)=NFY_JFu_PublicDigest11.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest11.window]
  exact NFY_JFu_PublicDigest11.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 624 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest11
-- END copied JFt_Digest11
-- BEGIN copied JFt_Digest12: lean/JFt_Digest12.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest12
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,1800828893#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest12.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest12.window
    NFY_JFu_PublicDigest12.length NFY_JFu_PublicDigest12.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest12.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest12.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 656 32 (by decide)=NFY_JFu_PublicDigest12.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest12.window]
  exact NFY_JFu_PublicDigest12.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 656 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest12
-- END copied JFt_Digest12
-- BEGIN copied JFt_Digest13: lean/JFt_Digest13.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest13
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,1280042062#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest13.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest13.window
    NFY_JFu_PublicDigest13.length NFY_JFu_PublicDigest13.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest13.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest13.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 688 32 (by decide)=NFY_JFu_PublicDigest13.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest13.window]
  exact NFY_JFu_PublicDigest13.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 688 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest13
-- END copied JFt_Digest13
-- BEGIN copied JFt_Digest14: lean/JFt_Digest14.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest14
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,2053396184#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest14.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest14.window
    NFY_JFu_PublicDigest14.length NFY_JFu_PublicDigest14.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest14.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest14.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 720 32 (by decide)=NFY_JFu_PublicDigest14.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest14.window]
  exact NFY_JFu_PublicDigest14.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 720 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest14
-- END copied JFt_Digest14
-- BEGIN copied JFt_Digest15: lean/JFt_Digest15.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest15
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,958210542#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest15.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest15.window
    NFY_JFu_PublicDigest15.length NFY_JFu_PublicDigest15.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest15.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest15.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 752 32 (by decide)=NFY_JFu_PublicDigest15.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest15.window]
  exact NFY_JFu_PublicDigest15.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 752 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest15
-- END copied JFt_Digest15
-- BEGIN copied JFt_Digest16: lean/JFt_Digest16.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest16
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,1680224983#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest16.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest16.window
    NFY_JFu_PublicDigest16.length NFY_JFu_PublicDigest16.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest16.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest16.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 784 32 (by decide)=NFY_JFu_PublicDigest16.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest16.window]
  exact NFY_JFu_PublicDigest16.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 784 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest16
-- END copied JFt_Digest16
-- BEGIN copied JFt_Digest17: lean/JFt_Digest17.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest17
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,1214723477#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest17.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest17.window
    NFY_JFu_PublicDigest17.length NFY_JFu_PublicDigest17.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest17.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest17.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 816 32 (by decide)=NFY_JFu_PublicDigest17.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest17.window]
  exact NFY_JFu_PublicDigest17.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 816 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest17
-- END copied JFt_Digest17
-- BEGIN copied JFt_Digest18: lean/JFt_Digest18.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest18
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,2083375353#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest18.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest18.window
    NFY_JFu_PublicDigest18.length NFY_JFu_PublicDigest18.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest18.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest18.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 848 32 (by decide)=NFY_JFu_PublicDigest18.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest18.window]
  exact NFY_JFu_PublicDigest18.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 848 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest18
-- END copied JFt_Digest18
-- BEGIN copied JFt_Digest19: lean/JFt_Digest19.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest19
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,1299980413#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest19.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest19.window
    NFY_JFu_PublicDigest19.length NFY_JFu_PublicDigest19.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest19.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest19.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 880 32 (by decide)=NFY_JFu_PublicDigest19.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest19.window]
  exact NFY_JFu_PublicDigest19.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 880 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest19
-- END copied JFt_Digest19
-- BEGIN copied JFt_Digest20: lean/JFt_Digest20.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest20
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,450526803#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest20.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest20.window
    NFY_JFu_PublicDigest20.length NFY_JFu_PublicDigest20.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest20.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest20.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 912 32 (by decide)=NFY_JFu_PublicDigest20.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest20.window]
  exact NFY_JFu_PublicDigest20.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 912 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest20
-- END copied JFt_Digest20
-- BEGIN copied JFt_Digest21: lean/JFt_Digest21.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest21
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,665567443#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest21.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest21.window
    NFY_JFu_PublicDigest21.length NFY_JFu_PublicDigest21.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest21.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest21.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 944 32 (by decide)=NFY_JFu_PublicDigest21.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest21.window]
  exact NFY_JFu_PublicDigest21.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 944 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest21
-- END copied JFt_Digest21
-- BEGIN copied JFt_SnapshotAcceptance: lean/JFt_SnapshotAcceptance.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_SnapshotAcceptance
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

theorem source (s : PoolV1PairLiveSnapshotV1)
    (pool : s.pool=NFY_JFu_PublicBindings.pool) (domain : s.deployment_domain=NFY_JFu_PublicBindings.domain)
    (sequence : s.sequence=13#u64) (index : s.next_pair_index=13#u64)
    (root : AspisS6NativeSnapshotReadDigest.read_digest (NFY_JFu_PublicRange.segment 304 32 (by decide))=
      ok (.Ok s.current_root))
    (frontier : ∀ i : Fin 20,AspisS6NativeSnapshotReadDigest.read_digest
      (NFY_JFu_PublicRange.segment (336+32*i.val) 32 (by have h:=i.isLt;omega))=
      ok (.Ok (s.frontier.val[i.val]'(by simpa only [s.frontier.property,show (20#usize).val=20 from rfl] using i.isLt)))) :
    validate_pool_v1_pair_live_snapshot_v1 s=ok (.Ok ()) := by
  apply NFY_JFu_SnapshotValidator.source s
  · rw [pool];exact NFY_JFu_PublicBindings.pool_nonzero
  · rw [domain];exact NFY_JFu_PublicBindings.domain_nonzero
  · rw [sequence,index]
  · rw [index];decide
  · exact NFY_JFu_DigestSliceCanonical.source _ _ root
  · intro i
    exact NFY_JFu_DigestSliceCanonical.source _ _ (frontier i)

#print axioms source
end AspisR1.NFY_JFt_SnapshotAcceptance
-- END copied JFt_SnapshotAcceptance

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
