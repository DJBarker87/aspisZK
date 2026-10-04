import AspisR156FullFreeze.FunsCore
import AspisV8R19.R144BeforeOodBytesBridge
import AspisV8R19.R196CurrentByteWriter
import Mathlib.Tactic

set_option autoImplicit false

namespace AspisV8R19.R567ClaimSerializationInjectivity
open Aeneas Aeneas.Std
open AspisR156FullFreeze.aspis_core
open AspisV8R19.R144BeforeOodBytesBridge
open AspisV8R19.R196CurrentByteWriter

theorem u32_to_le_bytes_injective (x y : U32)
    (h : (core.num.U32.to_le_bytes x).val = (core.num.U32.to_le_bytes y).val) :
  x = y := by
  have hbytes : x.bv.toLEBytes = y.bv.toLEBytes := by
    have hmap := congrArg (fun a : List U8 => a.map U8.bv) h
    simpa [core.num.U32.to_le_bytes] using hmap
  have hnat := congrArg (fun bs : List (BitVec 8) =>
    (BitVec.fromLEBytes bs).toNat) hbytes
  have hx := BitVec.fromLEBytes_toLEBytes (w := 32) (by decide) x.bv
  have hy := BitVec.fromLEBytes_toLEBytes (w := 32) (by decide) y.bv
  rw [hx, hy] at hnat
  have hval : x.bv.toNat = y.bv.toNat := by
    simpa only [BitVec.toNat_cast] using hnat
  have hbv : x.bv = y.bv := BitVec.eq_of_toNat_eq hval
  cases x with
  | mk x0 =>
    cases y with
    | mk y0 =>
      simp_all

theorem cm31_bytes_injective (x y : AspisR137Transcript.field.CM31)
    (h : cm31Bytes x = cm31Bytes y) : x = y := by
  have hlen : (core.num.U32.to_le_bytes x.a).val.length =
      (core.num.U32.to_le_bytes y.a).val.length := by
    simp [Array.length_eq]
  rcases List.append_inj h hlen with ⟨ha,hb⟩
  cases x with
  | mk xa xb =>
    cases y with
    | mk ya yb =>
      simp only [cm31Bytes] at ha hb
      have heq_a : xa = ya := u32_to_le_bytes_injective xa ya ha
      have heq_b : xb = yb := u32_to_le_bytes_injective xb yb hb
      simp [heq_a, heq_b]

theorem current_qm31_bytes_injective (x y : field.QM31)
    (h : qm31Bytes (toBefore x) = qm31Bytes (toBefore y)) : x = y := by
  have hlen : (cm31Bytes (AspisR136BeforeOod.toR137QM31 (toBefore x)).c0).length =
      (cm31Bytes (AspisR136BeforeOod.toR137QM31 (toBefore y)).c0).length := by
    simp [cm31Bytes_length]
  rcases List.append_inj h hlen with ⟨h0,h1⟩
  have hq0 : (AspisR136BeforeOod.toR137QM31 (toBefore x)).c0 =
      (AspisR136BeforeOod.toR137QM31 (toBefore y)).c0 :=
    cm31_bytes_injective _ _ h0
  have hq1 : (AspisR136BeforeOod.toR137QM31 (toBefore x)).c1 =
      (AspisR136BeforeOod.toR137QM31 (toBefore y)).c1 :=
    cm31_bytes_injective _ _ h1
  have h0a : x.c0.a = y.c0.a := by
    have h := congrArg (fun z : AspisR137Transcript.field.CM31 => z.a) hq0
    simpa [toBefore, AspisR136BeforeOod.toR137QM31,
      AspisR136BeforeOod.toR137CM31] using h
  have h0b : x.c0.b = y.c0.b := by
    have h := congrArg (fun z : AspisR137Transcript.field.CM31 => z.b) hq0
    simpa [toBefore, AspisR136BeforeOod.toR137QM31,
      AspisR136BeforeOod.toR137CM31] using h
  have h1a : x.c1.a = y.c1.a := by
    have h := congrArg (fun z : AspisR137Transcript.field.CM31 => z.a) hq1
    simpa [toBefore, AspisR136BeforeOod.toR137QM31,
      AspisR136BeforeOod.toR137CM31] using h
  have h1b : x.c1.b = y.c1.b := by
    have h := congrArg (fun z : AspisR137Transcript.field.CM31 => z.b) hq1
    simpa [toBefore, AspisR136BeforeOod.toR137QM31,
      AspisR136BeforeOod.toR137CM31] using h
  cases x with
  | mk x0 x1 =>
    cases y with
    | mk y0 y1 =>
      cases x0 with
      | mk x00 x01 =>
        cases y0 with
        | mk y00 y01 =>
          cases x1 with
          | mk x10 x11 =>
            cases y1 with
            | mk y10 y11 =>
              simp_all

#print axioms u32_to_le_bytes_injective
#print axioms cm31_bytes_injective
#print axioms current_qm31_bytes_injective
end AspisV8R19.R567ClaimSerializationInjectivity
