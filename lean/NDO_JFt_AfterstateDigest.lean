import NDO_JFt_DigestArray
import NDO_JFt_AfterstateValue
import NDO_JFt_Metadata
set_option autoImplicit false
namespace AspisR1.JFt_AfterstateDigest
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

def bytes22 : Array U8 32#usize := ⟨JFu_PublicDigest22.bytes,JFu_PublicDigest22.length⟩

theorem selected22 : (JFu_PublicRange.segment 992 32 (by decide)).val=bytes22.val := by
  dsimp only [JFu_PublicRange.segment,bytes22]
  exact JFu_PublicDigest22.selected

theorem exact22 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 992 32 (by decide))=ok (.Ok bytes22) :=
  JFt_ExactArray.source _ _ _ selected22

theorem decode22 : atomic_statement.decode_digest_canonical bytes22=ok (.Ok JFt_Digest22.value) :=
  JFt_DigestArray.source _ _ selected22 _ JFt_Digest22.source

def bytes23 : Array U8 32#usize := ⟨JFu_PublicDigest23.bytes,JFu_PublicDigest23.length⟩

theorem selected23 : (JFu_PublicRange.segment 1024 32 (by decide)).val=bytes23.val := by
  dsimp only [JFu_PublicRange.segment,bytes23]
  exact JFu_PublicDigest23.selected

theorem exact23 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1024 32 (by decide))=ok (.Ok bytes23) :=
  JFt_ExactArray.source _ _ _ selected23

theorem decode23 : atomic_statement.decode_digest_canonical bytes23=ok (.Ok JFt_Digest23.value) :=
  JFt_DigestArray.source _ _ selected23 _ JFt_Digest23.source

def bytes24 : Array U8 32#usize := ⟨JFu_PublicDigest24.bytes,JFu_PublicDigest24.length⟩

theorem selected24 : (JFu_PublicRange.segment 1056 32 (by decide)).val=bytes24.val := by
  dsimp only [JFu_PublicRange.segment,bytes24]
  exact JFu_PublicDigest24.selected

theorem exact24 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1056 32 (by decide))=ok (.Ok bytes24) :=
  JFt_ExactArray.source _ _ _ selected24

theorem decode24 : atomic_statement.decode_digest_canonical bytes24=ok (.Ok JFt_Digest24.value) :=
  JFt_DigestArray.source _ _ selected24 _ JFt_Digest24.source

def bytes25 : Array U8 32#usize := ⟨JFu_PublicDigest25.bytes,JFu_PublicDigest25.length⟩

theorem selected25 : (JFu_PublicRange.segment 1088 32 (by decide)).val=bytes25.val := by
  dsimp only [JFu_PublicRange.segment,bytes25]
  exact JFu_PublicDigest25.selected

theorem exact25 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1088 32 (by decide))=ok (.Ok bytes25) :=
  JFt_ExactArray.source _ _ _ selected25

theorem decode25 : atomic_statement.decode_digest_canonical bytes25=ok (.Ok JFt_Digest25.value) :=
  JFt_DigestArray.source _ _ selected25 _ JFt_Digest25.source

def bytes26 : Array U8 32#usize := ⟨JFu_PublicDigest26.bytes,JFu_PublicDigest26.length⟩

theorem selected26 : (JFu_PublicRange.segment 1120 32 (by decide)).val=bytes26.val := by
  dsimp only [JFu_PublicRange.segment,bytes26]
  exact JFu_PublicDigest26.selected

theorem exact26 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1120 32 (by decide))=ok (.Ok bytes26) :=
  JFt_ExactArray.source _ _ _ selected26

theorem decode26 : atomic_statement.decode_digest_canonical bytes26=ok (.Ok JFt_Digest26.value) :=
  JFt_DigestArray.source _ _ selected26 _ JFt_Digest26.source

def bytes27 : Array U8 32#usize := ⟨JFu_PublicDigest27.bytes,JFu_PublicDigest27.length⟩

theorem selected27 : (JFu_PublicRange.segment 1152 32 (by decide)).val=bytes27.val := by
  dsimp only [JFu_PublicRange.segment,bytes27]
  exact JFu_PublicDigest27.selected

theorem exact27 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1152 32 (by decide))=ok (.Ok bytes27) :=
  JFt_ExactArray.source _ _ _ selected27

theorem decode27 : atomic_statement.decode_digest_canonical bytes27=ok (.Ok JFt_Digest27.value) :=
  JFt_DigestArray.source _ _ selected27 _ JFt_Digest27.source

def bytes28 : Array U8 32#usize := ⟨JFu_PublicDigest28.bytes,JFu_PublicDigest28.length⟩

theorem selected28 : (JFu_PublicRange.segment 1184 32 (by decide)).val=bytes28.val := by
  dsimp only [JFu_PublicRange.segment,bytes28]
  exact JFu_PublicDigest28.selected

theorem exact28 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1184 32 (by decide))=ok (.Ok bytes28) :=
  JFt_ExactArray.source _ _ _ selected28

theorem decode28 : atomic_statement.decode_digest_canonical bytes28=ok (.Ok JFt_Digest28.value) :=
  JFt_DigestArray.source _ _ selected28 _ JFt_Digest28.source

def bytes29 : Array U8 32#usize := ⟨JFu_PublicDigest29.bytes,JFu_PublicDigest29.length⟩

theorem selected29 : (JFu_PublicRange.segment 1216 32 (by decide)).val=bytes29.val := by
  dsimp only [JFu_PublicRange.segment,bytes29]
  exact JFu_PublicDigest29.selected

theorem exact29 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1216 32 (by decide))=ok (.Ok bytes29) :=
  JFt_ExactArray.source _ _ _ selected29

theorem decode29 : atomic_statement.decode_digest_canonical bytes29=ok (.Ok JFt_Digest29.value) :=
  JFt_DigestArray.source _ _ selected29 _ JFt_Digest29.source

def bytes30 : Array U8 32#usize := ⟨JFu_PublicDigest30.bytes,JFu_PublicDigest30.length⟩

theorem selected30 : (JFu_PublicRange.segment 1248 32 (by decide)).val=bytes30.val := by
  dsimp only [JFu_PublicRange.segment,bytes30]
  exact JFu_PublicDigest30.selected

theorem exact30 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1248 32 (by decide))=ok (.Ok bytes30) :=
  JFt_ExactArray.source _ _ _ selected30

theorem decode30 : atomic_statement.decode_digest_canonical bytes30=ok (.Ok JFt_Digest30.value) :=
  JFt_DigestArray.source _ _ selected30 _ JFt_Digest30.source

def bytes31 : Array U8 32#usize := ⟨JFu_PublicDigest31.bytes,JFu_PublicDigest31.length⟩

theorem selected31 : (JFu_PublicRange.segment 1280 32 (by decide)).val=bytes31.val := by
  dsimp only [JFu_PublicRange.segment,bytes31]
  exact JFu_PublicDigest31.selected

theorem exact31 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1280 32 (by decide))=ok (.Ok bytes31) :=
  JFt_ExactArray.source _ _ _ selected31

theorem decode31 : atomic_statement.decode_digest_canonical bytes31=ok (.Ok JFt_Digest31.value) :=
  JFt_DigestArray.source _ _ selected31 _ JFt_Digest31.source

def bytes32 : Array U8 32#usize := ⟨JFu_PublicDigest32.bytes,JFu_PublicDigest32.length⟩

theorem selected32 : (JFu_PublicRange.segment 1312 32 (by decide)).val=bytes32.val := by
  dsimp only [JFu_PublicRange.segment,bytes32]
  exact JFu_PublicDigest32.selected

theorem exact32 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1312 32 (by decide))=ok (.Ok bytes32) :=
  JFt_ExactArray.source _ _ _ selected32

theorem decode32 : atomic_statement.decode_digest_canonical bytes32=ok (.Ok JFt_Digest32.value) :=
  JFt_DigestArray.source _ _ selected32 _ JFt_Digest32.source

def bytes33 : Array U8 32#usize := ⟨JFu_PublicDigest33.bytes,JFu_PublicDigest33.length⟩

theorem selected33 : (JFu_PublicRange.segment 1344 32 (by decide)).val=bytes33.val := by
  dsimp only [JFu_PublicRange.segment,bytes33]
  exact JFu_PublicDigest33.selected

theorem exact33 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1344 32 (by decide))=ok (.Ok bytes33) :=
  JFt_ExactArray.source _ _ _ selected33

theorem decode33 : atomic_statement.decode_digest_canonical bytes33=ok (.Ok JFt_Digest33.value) :=
  JFt_DigestArray.source _ _ selected33 _ JFt_Digest33.source

def bytes34 : Array U8 32#usize := ⟨JFu_PublicDigest34.bytes,JFu_PublicDigest34.length⟩

theorem selected34 : (JFu_PublicRange.segment 1376 32 (by decide)).val=bytes34.val := by
  dsimp only [JFu_PublicRange.segment,bytes34]
  exact JFu_PublicDigest34.selected

theorem exact34 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1376 32 (by decide))=ok (.Ok bytes34) :=
  JFt_ExactArray.source _ _ _ selected34

theorem decode34 : atomic_statement.decode_digest_canonical bytes34=ok (.Ok JFt_Digest34.value) :=
  JFt_DigestArray.source _ _ selected34 _ JFt_Digest34.source

def bytes35 : Array U8 32#usize := ⟨JFu_PublicDigest35.bytes,JFu_PublicDigest35.length⟩

theorem selected35 : (JFu_PublicRange.segment 1408 32 (by decide)).val=bytes35.val := by
  dsimp only [JFu_PublicRange.segment,bytes35]
  exact JFu_PublicDigest35.selected

theorem exact35 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1408 32 (by decide))=ok (.Ok bytes35) :=
  JFt_ExactArray.source _ _ _ selected35

theorem decode35 : atomic_statement.decode_digest_canonical bytes35=ok (.Ok JFt_Digest35.value) :=
  JFt_DigestArray.source _ _ selected35 _ JFt_Digest35.source

def bytes36 : Array U8 32#usize := ⟨JFu_PublicDigest36.bytes,JFu_PublicDigest36.length⟩

theorem selected36 : (JFu_PublicRange.segment 1440 32 (by decide)).val=bytes36.val := by
  dsimp only [JFu_PublicRange.segment,bytes36]
  exact JFu_PublicDigest36.selected

theorem exact36 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1440 32 (by decide))=ok (.Ok bytes36) :=
  JFt_ExactArray.source _ _ _ selected36

theorem decode36 : atomic_statement.decode_digest_canonical bytes36=ok (.Ok JFt_Digest36.value) :=
  JFt_DigestArray.source _ _ selected36 _ JFt_Digest36.source

def bytes37 : Array U8 32#usize := ⟨JFu_PublicDigest37.bytes,JFu_PublicDigest37.length⟩

theorem selected37 : (JFu_PublicRange.segment 1472 32 (by decide)).val=bytes37.val := by
  dsimp only [JFu_PublicRange.segment,bytes37]
  exact JFu_PublicDigest37.selected

theorem exact37 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1472 32 (by decide))=ok (.Ok bytes37) :=
  JFt_ExactArray.source _ _ _ selected37

theorem decode37 : atomic_statement.decode_digest_canonical bytes37=ok (.Ok JFt_Digest37.value) :=
  JFt_DigestArray.source _ _ selected37 _ JFt_Digest37.source

def bytes38 : Array U8 32#usize := ⟨JFu_PublicDigest38.bytes,JFu_PublicDigest38.length⟩

theorem selected38 : (JFu_PublicRange.segment 1504 32 (by decide)).val=bytes38.val := by
  dsimp only [JFu_PublicRange.segment,bytes38]
  exact JFu_PublicDigest38.selected

theorem exact38 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1504 32 (by decide))=ok (.Ok bytes38) :=
  JFt_ExactArray.source _ _ _ selected38

theorem decode38 : atomic_statement.decode_digest_canonical bytes38=ok (.Ok JFt_Digest38.value) :=
  JFt_DigestArray.source _ _ selected38 _ JFt_Digest38.source

def bytes39 : Array U8 32#usize := ⟨JFu_PublicDigest39.bytes,JFu_PublicDigest39.length⟩

theorem selected39 : (JFu_PublicRange.segment 1536 32 (by decide)).val=bytes39.val := by
  dsimp only [JFu_PublicRange.segment,bytes39]
  exact JFu_PublicDigest39.selected

theorem exact39 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1536 32 (by decide))=ok (.Ok bytes39) :=
  JFt_ExactArray.source _ _ _ selected39

theorem decode39 : atomic_statement.decode_digest_canonical bytes39=ok (.Ok JFt_Digest39.value) :=
  JFt_DigestArray.source _ _ selected39 _ JFt_Digest39.source

def bytes40 : Array U8 32#usize := ⟨JFu_PublicDigest40.bytes,JFu_PublicDigest40.length⟩

theorem selected40 : (JFu_PublicRange.segment 1568 32 (by decide)).val=bytes40.val := by
  dsimp only [JFu_PublicRange.segment,bytes40]
  exact JFu_PublicDigest40.selected

theorem exact40 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1568 32 (by decide))=ok (.Ok bytes40) :=
  JFt_ExactArray.source _ _ _ selected40

theorem decode40 : atomic_statement.decode_digest_canonical bytes40=ok (.Ok JFt_Digest40.value) :=
  JFt_DigestArray.source _ _ selected40 _ JFt_Digest40.source

def bytes41 : Array U8 32#usize := ⟨JFu_PublicDigest41.bytes,JFu_PublicDigest41.length⟩

theorem selected41 : (JFu_PublicRange.segment 1600 32 (by decide)).val=bytes41.val := by
  dsimp only [JFu_PublicRange.segment,bytes41]
  exact JFu_PublicDigest41.selected

theorem exact41 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1600 32 (by decide))=ok (.Ok bytes41) :=
  JFt_ExactArray.source _ _ _ selected41

theorem decode41 : atomic_statement.decode_digest_canonical bytes41=ok (.Ok JFt_Digest41.value) :=
  JFt_DigestArray.source _ _ selected41 _ JFt_Digest41.source

def bytes42 : Array U8 32#usize := ⟨JFu_PublicDigest42.bytes,JFu_PublicDigest42.length⟩

theorem selected42 : (JFu_PublicRange.segment 1632 32 (by decide)).val=bytes42.val := by
  dsimp only [JFu_PublicRange.segment,bytes42]
  exact JFu_PublicDigest42.selected

theorem exact42 : pool_v1.pair_terminal.exact 32#usize
    (JFu_PublicRange.segment 1632 32 (by decide))=ok (.Ok bytes42) :=
  JFt_ExactArray.source _ _ _ selected42

theorem decode42 : atomic_statement.decode_digest_canonical bytes42=ok (.Ok JFt_Digest42.value) :=
  JFt_DigestArray.source _ _ selected42 _ JFt_Digest42.source

theorem next : pool_v1.pair_terminal.exact 8#usize
    (JFu_PublicRange.segment 984 8 (by decide))=ok (.Ok JFu_PublicIndices.after) := by
  have selected : (JFu_PublicRange.segment 984 8 (by decide)).val=JFu_PublicIndices.after.val := by
    dsimp only [JFu_PublicRange.segment]
    exact JFu_PublicIndices.next_bytes
  exact JFt_ExactArray.source _ _ _ selected

#print axioms next
#print axioms selected22
#print axioms exact22
#print axioms decode22
#print axioms selected23
#print axioms exact23
#print axioms decode23
#print axioms selected24
#print axioms exact24
#print axioms decode24
#print axioms selected25
#print axioms exact25
#print axioms decode25
#print axioms selected26
#print axioms exact26
#print axioms decode26
#print axioms selected27
#print axioms exact27
#print axioms decode27
#print axioms selected28
#print axioms exact28
#print axioms decode28
#print axioms selected29
#print axioms exact29
#print axioms decode29
#print axioms selected30
#print axioms exact30
#print axioms decode30
#print axioms selected31
#print axioms exact31
#print axioms decode31
#print axioms selected32
#print axioms exact32
#print axioms decode32
#print axioms selected33
#print axioms exact33
#print axioms decode33
#print axioms selected34
#print axioms exact34
#print axioms decode34
#print axioms selected35
#print axioms exact35
#print axioms decode35
#print axioms selected36
#print axioms exact36
#print axioms decode36
#print axioms selected37
#print axioms exact37
#print axioms decode37
#print axioms selected38
#print axioms exact38
#print axioms decode38
#print axioms selected39
#print axioms exact39
#print axioms decode39
#print axioms selected40
#print axioms exact40
#print axioms decode40
#print axioms selected41
#print axioms exact41
#print axioms decode41
#print axioms selected42
#print axioms exact42
#print axioms decode42
end AspisR1.JFt_AfterstateDigest
