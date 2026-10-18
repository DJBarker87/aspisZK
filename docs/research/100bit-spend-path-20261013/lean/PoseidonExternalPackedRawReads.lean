import Aeneas
import PoseidonLeadingSourceDeclarationsV5
import PoseidonExternalPackedRawOpsV7

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result WP
namespace AspisR1.PoseidonExternalPackedRawReads
open AspisR1SelectedMaskProbe

abbrev LocalRows := Array (Array U64 4#usize) 4#usize

def localWord (rows : LocalRows) (r j : Fin 4) : U64 :=
  (rows.val[r.val]'(by simpa [rows.property] using r.isLt)).val[j.val]'(by
    simpa [(rows.val[r.val]'(by simpa [rows.property] using r.isLt)).property] using j.isLt)

private theorem small_nat_usize (n : Nat) (hn : n < 4) :
    n < 2 ^ Std.UScalarTy.Usize.numBits := by
  have hpow : 4 < 2 ^ Std.UScalarTy.Usize.numBits := by
    rw [Std.UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
    have hmax := Usize.cMax_bound_concrete.1
    omega
  omega

private def u4 (i : Fin 4) : Usize :=
  Usize.ofNatCore i.val (small_nat_usize i.val i.isLt)

private theorem u4_val (i : Fin 4) : (u4 i).val = i.val := by
  simp [u4, UScalar.ofNatCore_val_eq]


/-- The exact two checked reads used to obtain one local packed limb. -/
def readWord (rows : LocalRows) (r j : Fin 4) : Result U64 := do
  let row ← Array.index_usize rows (u4 r)
  Array.index_usize row (u4 j)

theorem readWord_success (rows : LocalRows) (r j : Fin 4) :
    ∃ word, readWord rows r j = .ok word ∧ word = localWord rows r j := by
  have hbOuter : (u4 r).val < rows.length := by
    simpa [rows.property, u4_val] using r.isLt
  obtain ⟨row, hOuter, hvOuter⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec rows (u4 r) hbOuter)
  have hRow : row = rows.val[r.val]'(by simpa [rows.property] using r.isLt) := by
    simpa [u4_val] using hvOuter
  have hbInner : (u4 j).val < row.length := by
    simpa [row.property, u4_val] using j.isLt
  obtain ⟨word, hInner, hvInner⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec row (u4 j) hbInner)
  have hvInner' : word = localWord rows r j := by
    have hvInner1 : word = row.val[j.val]'(by simpa [row.property] using j.isLt) := by
      simpa [u4_val] using hvInner
    calc
      word = row.val[j.val]'(by simpa [row.property] using j.isLt) := hvInner1
      _ = (rows.val[r.val]'(by simpa [rows.property] using r.isLt)).val[j.val]'(by
            simpa [(rows.val[r.val]'(by simpa [rows.property] using r.isLt)).property] using j.isLt) :=
        congrArg (fun x : Array U64 4#usize =>
          x.val[j.val]'(by simpa [x.property] using j.isLt)) hRow
      _ = localWord rows r j := rfl
  refine ⟨word, ?_, hvInner'⟩
  simp only [readWord, hOuter, bind_tc_ok, hInner]

private def f0 : Fin 4 := ⟨0, by decide⟩
private def f1 : Fin 4 := ⟨1, by decide⟩
private def f2 : Fin 4 := ⟨2, by decide⟩
private def f3 : Fin 4 := ⟨3, by decide⟩

private theorem nat0_eq_f0 : (0 : Fin 4) = f0 := Fin.ext rfl
private theorem nat1_eq_f1 : (1 : Fin 4) = f1 := Fin.ext rfl
private theorem nat2_eq_f2 : (2 : Fin 4) = f2 := Fin.ext rfl
private theorem nat3_eq_f3 : (3 : Fin 4) = f3 := Fin.ext rfl

def component0ReadOps (bound : U64) (rows : LocalRows) : Result U64 := do
  let x00 ← readWord rows f0 f0
  let i1 ← 5#u64 * bound
  let i2 ← x00 + i1
  let x11 ← readWord rows f1 f1
  let i4 ← i2 - x11
  let x22 ← readWord rows f2 f2
  let i6 ← 2#u64 * x22
  let i7 ← i4 + i6
  let x23 ← readWord rows f2 f3
  let i9 ← i7 - x23
  let x32 ← readWord rows f3 f2
  let i11 ← i9 - x32
  let x33 ← readWord rows f3 f3
  let i13 ← 2#u64 * x33
  let i14 ← i11 - i13
  ok i14

theorem component0ReadOps_eq (bound : U64) (rows : LocalRows) :
    component0ReadOps bound rows =
      AspisR1.PoseidonExternalPackedRawOps.component0Ops bound
        (fun r j => localWord rows r j) := by
  obtain ⟨x00, h00, hv00⟩ := readWord_success rows f0 f0
  obtain ⟨x11, h11, hv11⟩ := readWord_success rows f1 f1
  obtain ⟨x22, h22, hv22⟩ := readWord_success rows f2 f2
  obtain ⟨x23, h23, hv23⟩ := readWord_success rows f2 f3
  obtain ⟨x32, h32, hv32⟩ := readWord_success rows f3 f2
  obtain ⟨x33, h33, hv33⟩ := readWord_success rows f3 f3
  simp only [f0, f1, f2, f3] at h00 h11 h22 h23 h32 h33 hv00 hv11 hv22 hv23 hv32 hv33
  simp only [component0ReadOps, f0, f1, f2, f3, h00, h11, h22, h23, h32, h33,
    bind_tc_ok, hv00, hv11, hv22, hv23, hv32, hv33,
    nat0_eq_f0, nat1_eq_f1, nat2_eq_f2, nat3_eq_f3,
    AspisR1.PoseidonExternalPackedRawOps.component0Ops]

def component1ReadOps (bound : U64) (rows : LocalRows) : Result U64 := do
  let x01 ← readWord rows f0 f1
  let x10 ← readWord rows f1 f0
  let i17 ← x01 + x10
  let x22 ← readWord rows f2 f2
  let i19 ← i17 + x22
  let x23 ← readWord rows f2 f3
  let i21 ← 2#u64 * x23
  let i22 ← i19 + i21
  let x32 ← readWord rows f3 f2
  let i24 ← 2#u64 * x32
  let i25 ← i22 + i24
  let i26 ← i25 + bound
  let x33 ← readWord rows f3 f3
  let i28 ← i26 - x33
  ok i28

theorem component1ReadOps_eq (bound : U64) (rows : LocalRows) :
    component1ReadOps bound rows =
      AspisR1.PoseidonExternalPackedRawOps.component1Ops bound
        (fun r j => localWord rows r j) := by
  obtain ⟨x01, h01, hv01⟩ := readWord_success rows f0 f1
  obtain ⟨x10, h10, hv10⟩ := readWord_success rows f1 f0
  obtain ⟨x22, h22, hv22⟩ := readWord_success rows f2 f2
  obtain ⟨x23, h23, hv23⟩ := readWord_success rows f2 f3
  obtain ⟨x32, h32, hv32⟩ := readWord_success rows f3 f2
  obtain ⟨x33, h33, hv33⟩ := readWord_success rows f3 f3
  simp only [f0, f1, f2, f3] at h01 h10 h22 h23 h32 h33 hv01 hv10 hv22 hv23 hv32 hv33
  simp only [component1ReadOps, f0, f1, f2, f3, h01, h10, h22, h23, h32, h33,
    bind_tc_ok, hv01, hv10, hv22, hv23, hv32, hv33,
    nat0_eq_f0, nat1_eq_f1, nat2_eq_f2, nat3_eq_f3,
    AspisR1.PoseidonExternalPackedRawOps.component1Ops]

def component2ReadOps (bound : U64) (rows : LocalRows) : Result U64 := do
  let x02 ← readWord rows f0 f2
  let i30 ← 2#u64 * bound
  let i31 ← x02 + i30
  let x13 ← readWord rows f1 f3
  let i33 ← i31 - x13
  let x20 ← readWord rows f2 f0
  let i35 ← i33 + x20
  let x31 ← readWord rows f3 f1
  let i37 ← i35 - x31
  ok i37

theorem component2ReadOps_eq (bound : U64) (rows : LocalRows) :
    component2ReadOps bound rows =
      AspisR1.PoseidonExternalPackedRawOps.component2Ops bound
        (fun r j => localWord rows r j) := by
  obtain ⟨x02, h02, hv02⟩ := readWord_success rows f0 f2
  obtain ⟨x13, h13, hv13⟩ := readWord_success rows f1 f3
  obtain ⟨x20, h20, hv20⟩ := readWord_success rows f2 f0
  obtain ⟨x31, h31, hv31⟩ := readWord_success rows f3 f1
  simp only [f0, f1, f2, f3] at h02 h13 h20 h31 hv02 hv13 hv20 hv31
  simp only [component2ReadOps, f0, f1, f2, f3, h02, h13, h20, h31,
    bind_tc_ok, hv02, hv13, hv20, hv31,
    nat0_eq_f0, nat1_eq_f1, nat2_eq_f2, nat3_eq_f3,
    AspisR1.PoseidonExternalPackedRawOps.component2Ops]

def component3ReadOps (rows : LocalRows) : Result U64 := do
  let x03 ← readWord rows f0 f3
  let x12 ← readWord rows f1 f2
  let i40 ← x03 + x12
  let x21 ← readWord rows f2 f1
  let i42 ← i40 + x21
  let x30 ← readWord rows f3 f0
  let i44 ← i42 + x30
  ok i44

theorem component3ReadOps_eq (rows : LocalRows) :
    component3ReadOps rows =
      AspisR1.PoseidonExternalPackedRawOps.component3Ops
        (fun r j => localWord rows r j) := by
  obtain ⟨x03, h03, hv03⟩ := readWord_success rows f0 f3
  obtain ⟨x12, h12, hv12⟩ := readWord_success rows f1 f2
  obtain ⟨x21, h21, hv21⟩ := readWord_success rows f2 f1
  obtain ⟨x30, h30, hv30⟩ := readWord_success rows f3 f0
  simp only [f0, f1, f2, f3] at h03 h12 h21 h30 hv03 hv12 hv21 hv30
  simp only [component3ReadOps, f0, f1, f2, f3, h03, h12, h21, h30,
    bind_tc_ok, hv03, hv12, hv21, hv30,
    nat0_eq_f0, nat1_eq_f1, nat2_eq_f2, nat3_eq_f3,
    AspisR1.PoseidonExternalPackedRawOps.component3Ops]

def externalLocalRawTail (bound : U64) (rows : LocalRows) :
    Result (Array U64 4#usize) := do
  let x0 ← component0ReadOps bound rows
  let x1 ← component1ReadOps bound rows
  let x2 ← component2ReadOps bound rows
  let x3 ← component3ReadOps rows
  ok (Array.make 4#usize [x0, x1, x2, x3])

theorem externalLocalRawTail_success (bound : U64) (rows : LocalRows)
    (hbound : ∀ r j, (localWord rows r j).val < bound.val)
    (hwide : 8 * bound.val < 2^64) :
    ∃ out : Array U64 4#usize,
      externalLocalRawTail bound rows = .ok out ∧
      ∀ j : Fin 4,
        out.val[j.val]'(by simpa using j.isLt) =
          AspisR1.PoseidonExternalPackedAlgebra.packedNat
            bound.val (fun r k => (localWord rows r k).val) j := by
  have h0 := component0ReadOps_eq bound rows
  have h1 := component1ReadOps_eq bound rows
  have h2 := component2ReadOps_eq bound rows
  have h3 := component3ReadOps_eq rows
  have hcomponents :=
    AspisR1.PoseidonExternalPackedRawOps.packedComponentsOps_success bound
      (fun r j => localWord rows r j) hbound hwide
  obtain ⟨out, hout, hvalues⟩ := hcomponents
  refine ⟨out, ?_, hvalues⟩
  simpa [externalLocalRawTail,
    AspisR1.PoseidonExternalPackedRawOps.packedComponentsOps, h0, h1, h2, h3]
    using hout

#print axioms readWord_success
end AspisR1.PoseidonExternalPackedRawReads
