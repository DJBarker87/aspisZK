import FJl_FixedIndex
import R1MixedLeafDecoder
set_option autoImplicit false
namespace AspisR1.FJl_C1Coordinates
open ExactLeafFieldCodec MixedLeafEncoding MixedLeafDecoder
/-- Coordinate extraction from the strict SAME C1 decoded bytes. -/
theorem slot (bytes : List Byte) (c : C1) (run : decodeC1 bytes=some c) (s : Fin 4) :
    decodeC1Slot ((bytes.drop (120*s.val)).take 120)=some (c s) :=
  FJl_FixedIndex.read _ _ _ bytes c run s

theorem scalar (bytes : List Byte) (c : C1) (run : decodeC1 bytes=some c)
    (s : Fin 4) (l : Fin 26) :
    decodeM31 ((((bytes.drop (120*s.val)).take 120).take 104).drop (4*l.val) |>.take 4)=
      some ((c s).1 l) := by
  have h := slot bytes c run s
  unfold decodeC1Slot at h
  cases hw : FixedWidthDecoder.decode decodeM31 4 26
      (((bytes.drop (120*s.val)).take 120).take 104) with
  | none => simp only [hw,Option.bind_eq_bind,Option.bind_none,reduceCtorEq] at h
  | some words =>
    cases ht : decodeQM31 (((bytes.drop (120*s.val)).take 120).drop 104) with
    | none => simp only [hw,ht,Option.bind_eq_bind,Option.bind_some,Option.bind_none,reduceCtorEq] at h
    | some tail =>
      have same : (words,tail)=c s := by simpa only [hw,ht,Option.bind_eq_bind,Option.bind_some,Option.pure_def,Option.some.injEq] using h
      rw [←same]
      exact FJl_FixedIndex.read _ _ _ _ words hw l

theorem tail (bytes : List Byte) (c : C1) (run : decodeC1 bytes=some c) (s : Fin 4) :
    decodeQM31 (((bytes.drop (120*s.val)).take 120).drop 104)=some (c s).2 := by
  have h := slot bytes c run s
  unfold decodeC1Slot at h
  cases hw : FixedWidthDecoder.decode decodeM31 4 26
      (((bytes.drop (120*s.val)).take 120).take 104) with
  | none => simp only [hw,Option.bind_eq_bind,Option.bind_none,reduceCtorEq] at h
  | some words =>
    cases ht : decodeQM31 (((bytes.drop (120*s.val)).take 120).drop 104) with
    | none => simp only [hw,ht,Option.bind_eq_bind,Option.bind_some,Option.bind_none,reduceCtorEq] at h
    | some tail =>
      have same : (words,tail)=c s := by simpa only [hw,ht,Option.bind_eq_bind,Option.bind_some,Option.pure_def,Option.some.injEq] using h
      rw [←same]
#print axioms slot
#print axioms scalar
#print axioms tail
end AspisR1.FJl_C1Coordinates
