import Lean
import NFY_Part033
import NFY_Part034
import RPz7_S6NativeAfterstateDecoderFactoredV1
import NFY_Part021
import NFY_Part020

-- BEGIN copied JFt_AfterstateDigest: lean/JFt_AfterstateDigest.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_AfterstateDigest
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

def bytes22 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest22.bytes,NFY_JFu_PublicDigest22.length⟩

theorem selected22 : (NFY_JFu_PublicRange.segment 992 32 (by decide)).val=bytes22.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes22]
  exact NFY_JFu_PublicDigest22.selected

theorem exact22 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 992 32 (by decide))=ok (.Ok bytes22) :=
  NFY_JFt_ExactArray.source _ _ _ selected22

theorem decode22 : atomic_statement.decode_digest_canonical bytes22=ok (.Ok NFY_JFt_Digest22.value) :=
  NFY_JFt_DigestArray.source _ _ selected22 _ NFY_JFt_Digest22.source

def bytes23 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest23.bytes,NFY_JFu_PublicDigest23.length⟩

theorem selected23 : (NFY_JFu_PublicRange.segment 1024 32 (by decide)).val=bytes23.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes23]
  exact NFY_JFu_PublicDigest23.selected

theorem exact23 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1024 32 (by decide))=ok (.Ok bytes23) :=
  NFY_JFt_ExactArray.source _ _ _ selected23

theorem decode23 : atomic_statement.decode_digest_canonical bytes23=ok (.Ok NFY_JFt_Digest23.value) :=
  NFY_JFt_DigestArray.source _ _ selected23 _ NFY_JFt_Digest23.source

def bytes24 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest24.bytes,NFY_JFu_PublicDigest24.length⟩

theorem selected24 : (NFY_JFu_PublicRange.segment 1056 32 (by decide)).val=bytes24.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes24]
  exact NFY_JFu_PublicDigest24.selected

theorem exact24 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1056 32 (by decide))=ok (.Ok bytes24) :=
  NFY_JFt_ExactArray.source _ _ _ selected24

theorem decode24 : atomic_statement.decode_digest_canonical bytes24=ok (.Ok NFY_JFt_Digest24.value) :=
  NFY_JFt_DigestArray.source _ _ selected24 _ NFY_JFt_Digest24.source

def bytes25 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest25.bytes,NFY_JFu_PublicDigest25.length⟩

theorem selected25 : (NFY_JFu_PublicRange.segment 1088 32 (by decide)).val=bytes25.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes25]
  exact NFY_JFu_PublicDigest25.selected

theorem exact25 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1088 32 (by decide))=ok (.Ok bytes25) :=
  NFY_JFt_ExactArray.source _ _ _ selected25

theorem decode25 : atomic_statement.decode_digest_canonical bytes25=ok (.Ok NFY_JFt_Digest25.value) :=
  NFY_JFt_DigestArray.source _ _ selected25 _ NFY_JFt_Digest25.source

def bytes26 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest26.bytes,NFY_JFu_PublicDigest26.length⟩

theorem selected26 : (NFY_JFu_PublicRange.segment 1120 32 (by decide)).val=bytes26.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes26]
  exact NFY_JFu_PublicDigest26.selected

theorem exact26 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1120 32 (by decide))=ok (.Ok bytes26) :=
  NFY_JFt_ExactArray.source _ _ _ selected26

theorem decode26 : atomic_statement.decode_digest_canonical bytes26=ok (.Ok NFY_JFt_Digest26.value) :=
  NFY_JFt_DigestArray.source _ _ selected26 _ NFY_JFt_Digest26.source

def bytes27 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest27.bytes,NFY_JFu_PublicDigest27.length⟩

theorem selected27 : (NFY_JFu_PublicRange.segment 1152 32 (by decide)).val=bytes27.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes27]
  exact NFY_JFu_PublicDigest27.selected

theorem exact27 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1152 32 (by decide))=ok (.Ok bytes27) :=
  NFY_JFt_ExactArray.source _ _ _ selected27

theorem decode27 : atomic_statement.decode_digest_canonical bytes27=ok (.Ok NFY_JFt_Digest27.value) :=
  NFY_JFt_DigestArray.source _ _ selected27 _ NFY_JFt_Digest27.source

def bytes28 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest28.bytes,NFY_JFu_PublicDigest28.length⟩

theorem selected28 : (NFY_JFu_PublicRange.segment 1184 32 (by decide)).val=bytes28.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes28]
  exact NFY_JFu_PublicDigest28.selected

theorem exact28 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1184 32 (by decide))=ok (.Ok bytes28) :=
  NFY_JFt_ExactArray.source _ _ _ selected28

theorem decode28 : atomic_statement.decode_digest_canonical bytes28=ok (.Ok NFY_JFt_Digest28.value) :=
  NFY_JFt_DigestArray.source _ _ selected28 _ NFY_JFt_Digest28.source

def bytes29 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest29.bytes,NFY_JFu_PublicDigest29.length⟩

theorem selected29 : (NFY_JFu_PublicRange.segment 1216 32 (by decide)).val=bytes29.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes29]
  exact NFY_JFu_PublicDigest29.selected

theorem exact29 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1216 32 (by decide))=ok (.Ok bytes29) :=
  NFY_JFt_ExactArray.source _ _ _ selected29

theorem decode29 : atomic_statement.decode_digest_canonical bytes29=ok (.Ok NFY_JFt_Digest29.value) :=
  NFY_JFt_DigestArray.source _ _ selected29 _ NFY_JFt_Digest29.source

def bytes30 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest30.bytes,NFY_JFu_PublicDigest30.length⟩

theorem selected30 : (NFY_JFu_PublicRange.segment 1248 32 (by decide)).val=bytes30.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes30]
  exact NFY_JFu_PublicDigest30.selected

theorem exact30 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1248 32 (by decide))=ok (.Ok bytes30) :=
  NFY_JFt_ExactArray.source _ _ _ selected30

theorem decode30 : atomic_statement.decode_digest_canonical bytes30=ok (.Ok NFY_JFt_Digest30.value) :=
  NFY_JFt_DigestArray.source _ _ selected30 _ NFY_JFt_Digest30.source

def bytes31 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest31.bytes,NFY_JFu_PublicDigest31.length⟩

theorem selected31 : (NFY_JFu_PublicRange.segment 1280 32 (by decide)).val=bytes31.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes31]
  exact NFY_JFu_PublicDigest31.selected

theorem exact31 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1280 32 (by decide))=ok (.Ok bytes31) :=
  NFY_JFt_ExactArray.source _ _ _ selected31

theorem decode31 : atomic_statement.decode_digest_canonical bytes31=ok (.Ok NFY_JFt_Digest31.value) :=
  NFY_JFt_DigestArray.source _ _ selected31 _ NFY_JFt_Digest31.source

def bytes32 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest32.bytes,NFY_JFu_PublicDigest32.length⟩

theorem selected32 : (NFY_JFu_PublicRange.segment 1312 32 (by decide)).val=bytes32.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes32]
  exact NFY_JFu_PublicDigest32.selected

theorem exact32 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1312 32 (by decide))=ok (.Ok bytes32) :=
  NFY_JFt_ExactArray.source _ _ _ selected32

theorem decode32 : atomic_statement.decode_digest_canonical bytes32=ok (.Ok NFY_JFt_Digest32.value) :=
  NFY_JFt_DigestArray.source _ _ selected32 _ NFY_JFt_Digest32.source

def bytes33 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest33.bytes,NFY_JFu_PublicDigest33.length⟩

theorem selected33 : (NFY_JFu_PublicRange.segment 1344 32 (by decide)).val=bytes33.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes33]
  exact NFY_JFu_PublicDigest33.selected

theorem exact33 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1344 32 (by decide))=ok (.Ok bytes33) :=
  NFY_JFt_ExactArray.source _ _ _ selected33

theorem decode33 : atomic_statement.decode_digest_canonical bytes33=ok (.Ok NFY_JFt_Digest33.value) :=
  NFY_JFt_DigestArray.source _ _ selected33 _ NFY_JFt_Digest33.source

def bytes34 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest34.bytes,NFY_JFu_PublicDigest34.length⟩

theorem selected34 : (NFY_JFu_PublicRange.segment 1376 32 (by decide)).val=bytes34.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes34]
  exact NFY_JFu_PublicDigest34.selected

theorem exact34 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1376 32 (by decide))=ok (.Ok bytes34) :=
  NFY_JFt_ExactArray.source _ _ _ selected34

theorem decode34 : atomic_statement.decode_digest_canonical bytes34=ok (.Ok NFY_JFt_Digest34.value) :=
  NFY_JFt_DigestArray.source _ _ selected34 _ NFY_JFt_Digest34.source

def bytes35 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest35.bytes,NFY_JFu_PublicDigest35.length⟩

theorem selected35 : (NFY_JFu_PublicRange.segment 1408 32 (by decide)).val=bytes35.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes35]
  exact NFY_JFu_PublicDigest35.selected

theorem exact35 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1408 32 (by decide))=ok (.Ok bytes35) :=
  NFY_JFt_ExactArray.source _ _ _ selected35

theorem decode35 : atomic_statement.decode_digest_canonical bytes35=ok (.Ok NFY_JFt_Digest35.value) :=
  NFY_JFt_DigestArray.source _ _ selected35 _ NFY_JFt_Digest35.source

def bytes36 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest36.bytes,NFY_JFu_PublicDigest36.length⟩

theorem selected36 : (NFY_JFu_PublicRange.segment 1440 32 (by decide)).val=bytes36.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes36]
  exact NFY_JFu_PublicDigest36.selected

theorem exact36 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1440 32 (by decide))=ok (.Ok bytes36) :=
  NFY_JFt_ExactArray.source _ _ _ selected36

theorem decode36 : atomic_statement.decode_digest_canonical bytes36=ok (.Ok NFY_JFt_Digest36.value) :=
  NFY_JFt_DigestArray.source _ _ selected36 _ NFY_JFt_Digest36.source

def bytes37 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest37.bytes,NFY_JFu_PublicDigest37.length⟩

theorem selected37 : (NFY_JFu_PublicRange.segment 1472 32 (by decide)).val=bytes37.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes37]
  exact NFY_JFu_PublicDigest37.selected

theorem exact37 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1472 32 (by decide))=ok (.Ok bytes37) :=
  NFY_JFt_ExactArray.source _ _ _ selected37

theorem decode37 : atomic_statement.decode_digest_canonical bytes37=ok (.Ok NFY_JFt_Digest37.value) :=
  NFY_JFt_DigestArray.source _ _ selected37 _ NFY_JFt_Digest37.source

def bytes38 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest38.bytes,NFY_JFu_PublicDigest38.length⟩

theorem selected38 : (NFY_JFu_PublicRange.segment 1504 32 (by decide)).val=bytes38.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes38]
  exact NFY_JFu_PublicDigest38.selected

theorem exact38 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1504 32 (by decide))=ok (.Ok bytes38) :=
  NFY_JFt_ExactArray.source _ _ _ selected38

theorem decode38 : atomic_statement.decode_digest_canonical bytes38=ok (.Ok NFY_JFt_Digest38.value) :=
  NFY_JFt_DigestArray.source _ _ selected38 _ NFY_JFt_Digest38.source

def bytes39 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest39.bytes,NFY_JFu_PublicDigest39.length⟩

theorem selected39 : (NFY_JFu_PublicRange.segment 1536 32 (by decide)).val=bytes39.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes39]
  exact NFY_JFu_PublicDigest39.selected

theorem exact39 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1536 32 (by decide))=ok (.Ok bytes39) :=
  NFY_JFt_ExactArray.source _ _ _ selected39

theorem decode39 : atomic_statement.decode_digest_canonical bytes39=ok (.Ok NFY_JFt_Digest39.value) :=
  NFY_JFt_DigestArray.source _ _ selected39 _ NFY_JFt_Digest39.source

def bytes40 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest40.bytes,NFY_JFu_PublicDigest40.length⟩

theorem selected40 : (NFY_JFu_PublicRange.segment 1568 32 (by decide)).val=bytes40.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes40]
  exact NFY_JFu_PublicDigest40.selected

theorem exact40 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1568 32 (by decide))=ok (.Ok bytes40) :=
  NFY_JFt_ExactArray.source _ _ _ selected40

theorem decode40 : atomic_statement.decode_digest_canonical bytes40=ok (.Ok NFY_JFt_Digest40.value) :=
  NFY_JFt_DigestArray.source _ _ selected40 _ NFY_JFt_Digest40.source

def bytes41 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest41.bytes,NFY_JFu_PublicDigest41.length⟩

theorem selected41 : (NFY_JFu_PublicRange.segment 1600 32 (by decide)).val=bytes41.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes41]
  exact NFY_JFu_PublicDigest41.selected

theorem exact41 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1600 32 (by decide))=ok (.Ok bytes41) :=
  NFY_JFt_ExactArray.source _ _ _ selected41

theorem decode41 : atomic_statement.decode_digest_canonical bytes41=ok (.Ok NFY_JFt_Digest41.value) :=
  NFY_JFt_DigestArray.source _ _ selected41 _ NFY_JFt_Digest41.source

def bytes42 : Array U8 32#usize := ⟨NFY_JFu_PublicDigest42.bytes,NFY_JFu_PublicDigest42.length⟩

theorem selected42 : (NFY_JFu_PublicRange.segment 1632 32 (by decide)).val=bytes42.val := by
  dsimp only [NFY_JFu_PublicRange.segment,bytes42]
  exact NFY_JFu_PublicDigest42.selected

theorem exact42 : pool_v1.pair_terminal.exact 32#usize
    (NFY_JFu_PublicRange.segment 1632 32 (by decide))=ok (.Ok bytes42) :=
  NFY_JFt_ExactArray.source _ _ _ selected42

theorem decode42 : atomic_statement.decode_digest_canonical bytes42=ok (.Ok NFY_JFt_Digest42.value) :=
  NFY_JFt_DigestArray.source _ _ selected42 _ NFY_JFt_Digest42.source

theorem next : pool_v1.pair_terminal.exact 8#usize
    (NFY_JFu_PublicRange.segment 984 8 (by decide))=ok (.Ok NFY_JFu_PublicIndices.after) := by
  have selected : (NFY_JFu_PublicRange.segment 984 8 (by decide)).val=NFY_JFu_PublicIndices.after.val := by
    dsimp only [NFY_JFu_PublicRange.segment]
    exact NFY_JFu_PublicIndices.next_bytes
  exact NFY_JFt_ExactArray.source _ _ _ selected

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
end AspisR1.NFY_JFt_AfterstateDigest
-- END copied JFt_AfterstateDigest
-- BEGIN copied JFt_AfterstateTail: lean/JFt_AfterstateTail.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_AfterstateTail
open Aeneas Aeneas.Std Result
open AspisS6NativeAfterstateDecoderFactored

theorem source : part_16 NFY_JFu_PublicRange.afterstate NFY_JFt_Digest22.value NFY_JFt_Digest23.value NFY_JFt_Digest24.value NFY_JFt_Digest25.value NFY_JFt_Digest26.value NFY_JFt_Digest27.value NFY_JFt_Digest28.value NFY_JFt_Digest29.value NFY_JFt_Digest30.value NFY_JFt_Digest31.value NFY_JFt_Digest32.value NFY_JFt_Digest33.value NFY_JFt_Digest34.value NFY_JFt_Digest35.value NFY_JFt_Digest36.value NFY_JFt_Digest37.value NFY_JFt_Digest38.value=ok (.Ok NFY_JFt_AfterstateValue.value) := by
  unfold part_16
  simp only [NFY_JFu_PublicRange.afterstate,
    NFY_JFt_Range.read 976 688 (by decide) 560#usize 592#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 592#usize 624#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 624#usize 656#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 656#usize 688#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 8#usize 16#usize (by decide) (by decide),
    show (8#usize).val=8 from rfl,
    show (16#usize).val=16 from rfl,
    show (560#usize).val=560 from rfl,
    show (592#usize).val=592 from rfl,
    show (624#usize).val=624 from rfl,
    show (656#usize).val=656 from rfl,
    show (688#usize).val=688 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    NFY_JFt_AfterstateDigest.exact39,
    NFY_JFt_AfterstateDigest.decode39,
    NFY_JFt_AfterstateDigest.exact40,
    NFY_JFt_AfterstateDigest.decode40,
    NFY_JFt_AfterstateDigest.exact41,
    NFY_JFt_AfterstateDigest.decode41,
    NFY_JFt_AfterstateDigest.exact42,
    NFY_JFt_AfterstateDigest.decode42,
    NFY_JFt_AfterstateDigest.next,
    NFY_JFu_PublicIndices.next,
    lift,bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch]
  have validated:=NFY_JFt_AfterstateValue.validated
  unfold NFY_JFt_AfterstateValue.value at validated
  rw [validated]
  rfl

#print axioms source
end AspisR1.NFY_JFt_AfterstateTail
-- END copied JFt_AfterstateTail
-- BEGIN copied JFt_Afterstate12: lean/JFt_Afterstate12.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Afterstate12
open Aeneas Aeneas.Std Result
open AspisS6NativeAfterstateDecoderFactored

theorem source : part_12 NFY_JFu_PublicRange.afterstate NFY_JFt_Digest22.value NFY_JFt_Digest23.value NFY_JFt_Digest24.value NFY_JFt_Digest25.value NFY_JFt_Digest26.value NFY_JFt_Digest27.value NFY_JFt_Digest28.value NFY_JFt_Digest29.value NFY_JFt_Digest30.value NFY_JFt_Digest31.value NFY_JFt_Digest32.value NFY_JFt_Digest33.value NFY_JFt_Digest34.value=ok (.Ok NFY_JFt_AfterstateValue.value) := by
  have tail:=NFY_JFt_AfterstateTail.source
  unfold NFY_JFu_PublicRange.afterstate at tail
  unfold part_12
  simp only [NFY_JFu_PublicRange.afterstate,
    NFY_JFt_Range.read 976 688 (by decide) 432#usize 464#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 464#usize 496#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 496#usize 528#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 528#usize 560#usize (by decide) (by decide),
    show (432#usize).val=432 from rfl,
    show (464#usize).val=464 from rfl,
    show (496#usize).val=496 from rfl,
    show (528#usize).val=528 from rfl,
    show (560#usize).val=560 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    NFY_JFt_AfterstateDigest.exact35,
    NFY_JFt_AfterstateDigest.decode35,
    NFY_JFt_AfterstateDigest.exact36,
    NFY_JFt_AfterstateDigest.decode36,
    NFY_JFt_AfterstateDigest.exact37,
    NFY_JFt_AfterstateDigest.decode37,
    NFY_JFt_AfterstateDigest.exact38,
    NFY_JFt_AfterstateDigest.decode38,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.NFY_JFt_Afterstate12
-- END copied JFt_Afterstate12
-- BEGIN copied JFt_Afterstate08: lean/JFt_Afterstate08.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Afterstate08
open Aeneas Aeneas.Std Result
open AspisS6NativeAfterstateDecoderFactored

theorem source : part_8 NFY_JFu_PublicRange.afterstate NFY_JFt_Digest22.value NFY_JFt_Digest23.value NFY_JFt_Digest24.value NFY_JFt_Digest25.value NFY_JFt_Digest26.value NFY_JFt_Digest27.value NFY_JFt_Digest28.value NFY_JFt_Digest29.value NFY_JFt_Digest30.value=ok (.Ok NFY_JFt_AfterstateValue.value) := by
  have tail:=NFY_JFt_Afterstate12.source
  unfold NFY_JFu_PublicRange.afterstate at tail
  unfold part_8
  simp only [NFY_JFu_PublicRange.afterstate,
    NFY_JFt_Range.read 976 688 (by decide) 304#usize 336#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 336#usize 368#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 368#usize 400#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 400#usize 432#usize (by decide) (by decide),
    show (304#usize).val=304 from rfl,
    show (336#usize).val=336 from rfl,
    show (368#usize).val=368 from rfl,
    show (400#usize).val=400 from rfl,
    show (432#usize).val=432 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    NFY_JFt_AfterstateDigest.exact31,
    NFY_JFt_AfterstateDigest.decode31,
    NFY_JFt_AfterstateDigest.exact32,
    NFY_JFt_AfterstateDigest.decode32,
    NFY_JFt_AfterstateDigest.exact33,
    NFY_JFt_AfterstateDigest.decode33,
    NFY_JFt_AfterstateDigest.exact34,
    NFY_JFt_AfterstateDigest.decode34,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.NFY_JFt_Afterstate08
-- END copied JFt_Afterstate08
-- BEGIN copied JFt_Afterstate04: lean/JFt_Afterstate04.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Afterstate04
open Aeneas Aeneas.Std Result
open AspisS6NativeAfterstateDecoderFactored

theorem source : part_4 NFY_JFu_PublicRange.afterstate NFY_JFt_Digest22.value NFY_JFt_Digest23.value NFY_JFt_Digest24.value NFY_JFt_Digest25.value NFY_JFt_Digest26.value=ok (.Ok NFY_JFt_AfterstateValue.value) := by
  have tail:=NFY_JFt_Afterstate08.source
  unfold NFY_JFu_PublicRange.afterstate at tail
  unfold part_4
  simp only [NFY_JFu_PublicRange.afterstate,
    NFY_JFt_Range.read 976 688 (by decide) 176#usize 208#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 208#usize 240#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 240#usize 272#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 272#usize 304#usize (by decide) (by decide),
    show (176#usize).val=176 from rfl,
    show (208#usize).val=208 from rfl,
    show (240#usize).val=240 from rfl,
    show (272#usize).val=272 from rfl,
    show (304#usize).val=304 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    NFY_JFt_AfterstateDigest.exact27,
    NFY_JFt_AfterstateDigest.decode27,
    NFY_JFt_AfterstateDigest.exact28,
    NFY_JFt_AfterstateDigest.decode28,
    NFY_JFt_AfterstateDigest.exact29,
    NFY_JFt_AfterstateDigest.decode29,
    NFY_JFt_AfterstateDigest.exact30,
    NFY_JFt_AfterstateDigest.decode30,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.NFY_JFt_Afterstate04
-- END copied JFt_Afterstate04
-- BEGIN copied JFt_Afterstate00: lean/JFt_Afterstate00.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Afterstate00
open Aeneas Aeneas.Std Result
open AspisS6NativeAfterstateDecoderFactored

theorem source : part_0 NFY_JFu_PublicRange.afterstate NFY_JFt_Digest22.value=ok (.Ok NFY_JFt_AfterstateValue.value) := by
  have tail:=NFY_JFt_Afterstate04.source
  unfold NFY_JFu_PublicRange.afterstate at tail
  unfold part_0
  simp only [NFY_JFu_PublicRange.afterstate,
    NFY_JFt_Range.read 976 688 (by decide) 48#usize 80#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 80#usize 112#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 112#usize 144#usize (by decide) (by decide),
    NFY_JFt_Range.read 976 688 (by decide) 144#usize 176#usize (by decide) (by decide),
    show (48#usize).val=48 from rfl,
    show (80#usize).val=80 from rfl,
    show (112#usize).val=112 from rfl,
    show (144#usize).val=144 from rfl,
    show (176#usize).val=176 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    NFY_JFt_AfterstateDigest.exact23,
    NFY_JFt_AfterstateDigest.decode23,
    NFY_JFt_AfterstateDigest.exact24,
    NFY_JFt_AfterstateDigest.decode24,
    NFY_JFt_AfterstateDigest.exact25,
    NFY_JFt_AfterstateDigest.decode25,
    NFY_JFt_AfterstateDigest.exact26,
    NFY_JFt_AfterstateDigest.decode26,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.NFY_JFt_Afterstate00
-- END copied JFt_Afterstate00
-- BEGIN copied JFs_AfterstateSize: lean/JFs_AfterstateSize.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_AfterstateSize
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_terminal

theorem bytes : POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES=ok 688#usize := by
  unfold POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  obtain ⟨z,call,value⟩:=WP.spec_imp_exists
    (Usize.add_spec (x:=8#usize) (y:=680#usize) (by scalar_tac))
  have same : z=688#usize := by scalar_tac
  exact same ▸ call

theorem length : Slice.len NFY_JFu_PublicRange.afterstate=688#usize := by
  have h : NFY_JFu_PublicRange.afterstate.length=688 := NFY_JFu_PublicRange.length 976 688 (by decide)
  scalar_tac

#print axioms bytes
#print axioms length
end AspisR1.NFY_JFs_AfterstateSize
-- END copied JFs_AfterstateSize
-- BEGIN copied JFs_AfterstateDecode: lean/JFs_AfterstateDecode.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_AfterstateDecode
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_terminal

theorem factored : AspisS6NativeAfterstateDecoderFactored.decode NFY_JFu_PublicRange.afterstate=
    ok (.Ok NFY_JFt_AfterstateValue.value) := by
  have oneCheck : (1#u8 !=1#u8)=false := by decide
  have lengthCheck : (688#usize !=688#usize)=false := by decide
  have tail:=NFY_JFt_Afterstate00.source
  unfold NFY_JFu_PublicRange.afterstate at tail
  unfold AspisS6NativeAfterstateDecoderFactored.decode
  simp only [NFY_JFs_AfterstateSize.length,NFY_JFs_AfterstateSize.bytes,bind_tc_ok,lengthCheck,
    Bool.false_eq_true,↓reduceIte]
  simp only [NFY_JFu_PublicRange.afterstate,
    NFY_JFt_LocalWindow.firstn 976 688 4#usize (by decide) (by decide),
    show (4#usize).val=4 from rfl,NFY_JFs_AfterstateHeader.magic_selected,
    NFY_JFs_AfterstateHeader.magic_array,bind_tc_ok,NFY_JFs_AfterstateHeader.magic_compare,
    Bool.false_eq_true,↓reduceIte]
  have b4:=NFY_JFs_AfterstateHeader.b4
  have b5:=NFY_JFs_AfterstateHeader.b5
  have b6:=NFY_JFs_AfterstateHeader.b6
  have b7:=NFY_JFs_AfterstateHeader.b7
  unfold NFY_JFu_PublicRange.afterstate at b4 b5 b6 b7
  simp only [b4,b5,b6,b7,bind_tc_ok,
    POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION,
    pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,
    oneCheck,Bool.false_eq_true,↓reduceIte]
  simp only [NFY_JFt_Range.read 976 688 (by decide) 16#usize 48#usize (by decide) (by decide),
    show (16#usize).val=16 from rfl,show (48#usize).val=48 from rfl,
    Nat.reduceAdd,Nat.reduceSub,NFY_JFt_AfterstateDigest.exact22,NFY_JFt_AfterstateDigest.decode22,
    bind_tc_ok,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,tail]

theorem source : decode_pool_v1_pair_verified_afterstate_v1 NFY_JFu_PublicRange.afterstate=
    ok (.Ok NFY_JFt_AfterstateValue.value) :=
  (AspisS6NativeAfterstateDecoderFactored.decode_source _).symm.trans factored

#print axioms factored
#print axioms source
end AspisR1.NFY_JFs_AfterstateDecode
-- END copied JFs_AfterstateDecode
-- BEGIN copied JFt_Digest01: lean/JFt_Digest01.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest01
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1058347432#u32,1215059768#u32,718082286#u32,2029394131#u32,1184875844#u32,2099153903#u32,613239161#u32,1649887145#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest01.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest01.window
    NFY_JFu_PublicDigest01.length NFY_JFu_PublicDigest01.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest01.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest01.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 304 32 (by decide)=NFY_JFu_PublicDigest01.window := by
  apply Subtype.ext
  exact NFY_JFu_PublicDigest01.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 304 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest01
-- END copied JFt_Digest01
-- BEGIN copied JFt_Digest02: lean/JFt_Digest02.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest02
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [20384#u32,20401#u32,20418#u32,20435#u32,20452#u32,20469#u32,20486#u32,20503#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest02.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest02.window
    NFY_JFu_PublicDigest02.length NFY_JFu_PublicDigest02.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest02.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest02.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 336 32 (by decide)=NFY_JFu_PublicDigest02.window := by
  apply Subtype.ext
  exact NFY_JFu_PublicDigest02.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 336 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest02
-- END copied JFt_Digest02
-- BEGIN copied JFt_Digest03: lean/JFt_Digest03.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest03
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [141619947#u32,1448060902#u32,524379093#u32,1944458907#u32,1832113773#u32,579270723#u32,752346270#u32,1038346536#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest03.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest03.window
    NFY_JFu_PublicDigest03.length NFY_JFu_PublicDigest03.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest03.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest03.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 368 32 (by decide)=NFY_JFu_PublicDigest03.window := by
  apply Subtype.ext
  exact NFY_JFu_PublicDigest03.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 368 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest03
-- END copied JFt_Digest03

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
