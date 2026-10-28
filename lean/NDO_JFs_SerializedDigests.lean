import NDO_JFs_SerializedDigest
import NDO_JFt_PublicValues
import NDO_JFt_DigestArray
set_option autoImplicit false
namespace AspisR1.JFs_SerializedDigests
open Aeneas Aeneas.Std Result
open AspisR1PublicSerializer.FieldsRefinement431

theorem bytes00 : encodeWords JFt_Digest00.value.val=JFu_PublicDigest00.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest00.bytes,JFu_PublicDigest00.length⟩
  have selected : (JFu_PublicRange.segment 112 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest00.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest00.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes00

theorem bytes01 : encodeWords JFt_Digest01.value.val=JFu_PublicDigest01.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest01.bytes,JFu_PublicDigest01.length⟩
  have selected : (JFu_PublicRange.segment 304 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest01.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest01.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes01

theorem bytes02 : encodeWords JFt_Digest02.value.val=JFu_PublicDigest02.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest02.bytes,JFu_PublicDigest02.length⟩
  have selected : (JFu_PublicRange.segment 336 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest02.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest02.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes02

theorem bytes03 : encodeWords JFt_Digest03.value.val=JFu_PublicDigest03.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest03.bytes,JFu_PublicDigest03.length⟩
  have selected : (JFu_PublicRange.segment 368 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest03.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest03.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes03

theorem bytes04 : encodeWords JFt_Digest04.value.val=JFu_PublicDigest04.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest04.bytes,JFu_PublicDigest04.length⟩
  have selected : (JFu_PublicRange.segment 400 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest04.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest04.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes04

theorem bytes05 : encodeWords JFt_Digest05.value.val=JFu_PublicDigest05.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest05.bytes,JFu_PublicDigest05.length⟩
  have selected : (JFu_PublicRange.segment 432 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest05.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest05.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes05

theorem bytes06 : encodeWords JFt_Digest06.value.val=JFu_PublicDigest06.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest06.bytes,JFu_PublicDigest06.length⟩
  have selected : (JFu_PublicRange.segment 464 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest06.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest06.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes06

theorem bytes07 : encodeWords JFt_Digest07.value.val=JFu_PublicDigest07.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest07.bytes,JFu_PublicDigest07.length⟩
  have selected : (JFu_PublicRange.segment 496 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest07.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest07.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes07

theorem bytes08 : encodeWords JFt_Digest08.value.val=JFu_PublicDigest08.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest08.bytes,JFu_PublicDigest08.length⟩
  have selected : (JFu_PublicRange.segment 528 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest08.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest08.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes08

theorem bytes09 : encodeWords JFt_Digest09.value.val=JFu_PublicDigest09.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest09.bytes,JFu_PublicDigest09.length⟩
  have selected : (JFu_PublicRange.segment 560 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest09.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest09.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes09

theorem bytes10 : encodeWords JFt_Digest10.value.val=JFu_PublicDigest10.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest10.bytes,JFu_PublicDigest10.length⟩
  have selected : (JFu_PublicRange.segment 592 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest10.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest10.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes10

theorem bytes11 : encodeWords JFt_Digest11.value.val=JFu_PublicDigest11.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest11.bytes,JFu_PublicDigest11.length⟩
  have selected : (JFu_PublicRange.segment 624 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest11.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest11.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes11

theorem bytes12 : encodeWords JFt_Digest12.value.val=JFu_PublicDigest12.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest12.bytes,JFu_PublicDigest12.length⟩
  have selected : (JFu_PublicRange.segment 656 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest12.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest12.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes12

theorem bytes13 : encodeWords JFt_Digest13.value.val=JFu_PublicDigest13.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest13.bytes,JFu_PublicDigest13.length⟩
  have selected : (JFu_PublicRange.segment 688 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest13.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest13.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes13

theorem bytes14 : encodeWords JFt_Digest14.value.val=JFu_PublicDigest14.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest14.bytes,JFu_PublicDigest14.length⟩
  have selected : (JFu_PublicRange.segment 720 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest14.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest14.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes14

theorem bytes15 : encodeWords JFt_Digest15.value.val=JFu_PublicDigest15.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest15.bytes,JFu_PublicDigest15.length⟩
  have selected : (JFu_PublicRange.segment 752 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest15.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest15.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes15

theorem bytes16 : encodeWords JFt_Digest16.value.val=JFu_PublicDigest16.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest16.bytes,JFu_PublicDigest16.length⟩
  have selected : (JFu_PublicRange.segment 784 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest16.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest16.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes16

theorem bytes17 : encodeWords JFt_Digest17.value.val=JFu_PublicDigest17.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest17.bytes,JFu_PublicDigest17.length⟩
  have selected : (JFu_PublicRange.segment 816 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest17.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest17.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes17

theorem bytes18 : encodeWords JFt_Digest18.value.val=JFu_PublicDigest18.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest18.bytes,JFu_PublicDigest18.length⟩
  have selected : (JFu_PublicRange.segment 848 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest18.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest18.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes18

theorem bytes19 : encodeWords JFt_Digest19.value.val=JFu_PublicDigest19.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest19.bytes,JFu_PublicDigest19.length⟩
  have selected : (JFu_PublicRange.segment 880 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest19.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest19.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes19

theorem bytes20 : encodeWords JFt_Digest20.value.val=JFu_PublicDigest20.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest20.bytes,JFu_PublicDigest20.length⟩
  have selected : (JFu_PublicRange.segment 912 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest20.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest20.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes20

theorem bytes21 : encodeWords JFt_Digest21.value.val=JFu_PublicDigest21.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest21.bytes,JFu_PublicDigest21.length⟩
  have selected : (JFu_PublicRange.segment 944 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest21.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest21.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes21

theorem bytes22 : encodeWords JFt_Digest22.value.val=JFu_PublicDigest22.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest22.bytes,JFu_PublicDigest22.length⟩
  have selected : (JFu_PublicRange.segment 992 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest22.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest22.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes22

theorem bytes23 : encodeWords JFt_Digest23.value.val=JFu_PublicDigest23.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest23.bytes,JFu_PublicDigest23.length⟩
  have selected : (JFu_PublicRange.segment 1024 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest23.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest23.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes23

theorem bytes24 : encodeWords JFt_Digest24.value.val=JFu_PublicDigest24.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest24.bytes,JFu_PublicDigest24.length⟩
  have selected : (JFu_PublicRange.segment 1056 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest24.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest24.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes24

theorem bytes25 : encodeWords JFt_Digest25.value.val=JFu_PublicDigest25.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest25.bytes,JFu_PublicDigest25.length⟩
  have selected : (JFu_PublicRange.segment 1088 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest25.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest25.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes25

theorem bytes26 : encodeWords JFt_Digest26.value.val=JFu_PublicDigest26.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest26.bytes,JFu_PublicDigest26.length⟩
  have selected : (JFu_PublicRange.segment 1120 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest26.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest26.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes26

theorem bytes27 : encodeWords JFt_Digest27.value.val=JFu_PublicDigest27.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest27.bytes,JFu_PublicDigest27.length⟩
  have selected : (JFu_PublicRange.segment 1152 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest27.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest27.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes27

theorem bytes28 : encodeWords JFt_Digest28.value.val=JFu_PublicDigest28.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest28.bytes,JFu_PublicDigest28.length⟩
  have selected : (JFu_PublicRange.segment 1184 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest28.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest28.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes28

theorem bytes29 : encodeWords JFt_Digest29.value.val=JFu_PublicDigest29.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest29.bytes,JFu_PublicDigest29.length⟩
  have selected : (JFu_PublicRange.segment 1216 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest29.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest29.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes29

theorem bytes30 : encodeWords JFt_Digest30.value.val=JFu_PublicDigest30.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest30.bytes,JFu_PublicDigest30.length⟩
  have selected : (JFu_PublicRange.segment 1248 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest30.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest30.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes30

theorem bytes31 : encodeWords JFt_Digest31.value.val=JFu_PublicDigest31.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest31.bytes,JFu_PublicDigest31.length⟩
  have selected : (JFu_PublicRange.segment 1280 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest31.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest31.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes31

theorem bytes32 : encodeWords JFt_Digest32.value.val=JFu_PublicDigest32.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest32.bytes,JFu_PublicDigest32.length⟩
  have selected : (JFu_PublicRange.segment 1312 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest32.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest32.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes32

theorem bytes33 : encodeWords JFt_Digest33.value.val=JFu_PublicDigest33.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest33.bytes,JFu_PublicDigest33.length⟩
  have selected : (JFu_PublicRange.segment 1344 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest33.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest33.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes33

theorem bytes34 : encodeWords JFt_Digest34.value.val=JFu_PublicDigest34.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest34.bytes,JFu_PublicDigest34.length⟩
  have selected : (JFu_PublicRange.segment 1376 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest34.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest34.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes34

theorem bytes35 : encodeWords JFt_Digest35.value.val=JFu_PublicDigest35.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest35.bytes,JFu_PublicDigest35.length⟩
  have selected : (JFu_PublicRange.segment 1408 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest35.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest35.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes35

theorem bytes36 : encodeWords JFt_Digest36.value.val=JFu_PublicDigest36.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest36.bytes,JFu_PublicDigest36.length⟩
  have selected : (JFu_PublicRange.segment 1440 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest36.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest36.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes36

theorem bytes37 : encodeWords JFt_Digest37.value.val=JFu_PublicDigest37.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest37.bytes,JFu_PublicDigest37.length⟩
  have selected : (JFu_PublicRange.segment 1472 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest37.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest37.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes37

theorem bytes38 : encodeWords JFt_Digest38.value.val=JFu_PublicDigest38.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest38.bytes,JFu_PublicDigest38.length⟩
  have selected : (JFu_PublicRange.segment 1504 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest38.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest38.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes38

theorem bytes39 : encodeWords JFt_Digest39.value.val=JFu_PublicDigest39.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest39.bytes,JFu_PublicDigest39.length⟩
  have selected : (JFu_PublicRange.segment 1536 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest39.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest39.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes39

theorem bytes40 : encodeWords JFt_Digest40.value.val=JFu_PublicDigest40.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest40.bytes,JFu_PublicDigest40.length⟩
  have selected : (JFu_PublicRange.segment 1568 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest40.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest40.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes40

theorem bytes41 : encodeWords JFt_Digest41.value.val=JFu_PublicDigest41.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest41.bytes,JFu_PublicDigest41.length⟩
  have selected : (JFu_PublicRange.segment 1600 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest41.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest41.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes41

theorem bytes42 : encodeWords JFt_Digest42.value.val=JFu_PublicDigest42.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest42.bytes,JFu_PublicDigest42.length⟩
  have selected : (JFu_PublicRange.segment 1632 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest42.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest42.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes42

theorem bytes43 : encodeWords JFt_Digest43.value.val=JFu_PublicDigest43.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest43.bytes,JFu_PublicDigest43.length⟩
  have selected : (JFu_PublicRange.segment 1744 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest43.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest43.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes43

theorem bytes44 : encodeWords JFt_Digest44.value.val=JFu_PublicDigest44.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest44.bytes,JFu_PublicDigest44.length⟩
  have selected : (JFu_PublicRange.segment 1776 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest44.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest44.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes44

theorem bytes45 : encodeWords JFt_Digest45.value.val=JFu_PublicDigest45.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest45.bytes,JFu_PublicDigest45.length⟩
  have selected : (JFu_PublicRange.segment 1816 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest45.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest45.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes45

theorem bytes46 : encodeWords JFt_Digest46.value.val=JFu_PublicDigest46.bytes := by
  let bytes : Array U8 32#usize := ⟨JFu_PublicDigest46.bytes,JFu_PublicDigest46.length⟩
  have selected : (JFu_PublicRange.segment 1848 32 (by decide)).val=bytes.val := by
    dsimp only [JFu_PublicRange.segment,bytes]
    exact JFu_PublicDigest46.selected
  have call:=JFt_DigestArray.source _ bytes selected _ JFt_Digest46.source
  exact JFs_SerializedDigest.decoded bytes _ call
#print axioms bytes46
end AspisR1.JFs_SerializedDigests
