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
  have hfrom : BitVec.fromLEBytes x.bv.toLEBytes = BitVec.fromLEBytes y.bv.toLEBytes := by
    cases hbytes
    rfl
  have hx := BitVec.fromLEBytes_toLEBytes (w := 32) (by decide) x.bv
  have hy := BitVec.fromLEBytes_toLEBytes (w := 32) (by decide) y.bv
  rw [hx, hy] at hfrom
  have hbv : x.bv = y.bv := by
    simpa only [UScalarTy.U32_numBits_eq] using hfrom
  cases x
  cases y
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
  cases x
  cases y
  rcases hq0 with ⟨h0a,h0b⟩
  rcases hq1 with ⟨h1a,h1b⟩
  simp_all [toBefore, AspisR136BeforeOod.toR137QM31,
    AspisR136BeforeOod.toR137CM31]

#print axioms u32_to_le_bytes_injective
#print axioms cm31_bytes_injective
#print axioms current_qm31_bytes_injective
end AspisV8R19.R567ClaimSerializationInjectivity
