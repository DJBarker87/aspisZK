import RawPoseidonRowField
import PoseidonExternalColumn1Call
import PoseidonExternalColumn1Reassembly
import PoseidonRaw4Constructor
import RawPoseidonExtensionWords
import AspisR1.PoseidonFullRoundCellStep

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalColumn1ArrayCall
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalColumn1Call
open AspisR1.PoseidonExternalColumn1Reassembly
open AspisR1.PoseidonFullRoundCellStep
open AspisR1.RawPoseidonExtensionWords
open AspisR1.RawPoseidonRowField

abbrev QM := field.QM31
abbrev U32 := Std.U32
abbrev U64 := Std.U64
abbrev Limbs32 := Array U32 4#usize
abbrev Sums := Array (Array U64 4#usize) 4#usize
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM

def limbInputWords (limbs : Limbs32) : Fin 4 → Nat := fun j =>
  (limbs.val[j.val]'(by simpa [limbs.property] using j.isLt)).val

def column1Value (q : QM) (sums : Sums) (lane : Fin 4) (j : Fin 4) (v : U64) : Prop :=
  v.val = qWords q j + sumWords sums lane j

theorem source_success (q : QM) (sums : Sums) (lane : Usize)
    (hlane : lane.val < 16)
    (hsums : ∀ i j : Fin 4, (sumWordAt sums i j).val < 2^34) :
    ∃ raw : Array U64 4#usize, ∃ out : QM,
      (do
        let limbs ← state_only_poseidon.extension_limbs q
        let raw ← array_from_fn_copy 4#usize core.marker.CopyU64
          state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
          0#u64 (limbs,sums,lane)
        let out ← state_only_poseidon.extension_from_raw_limbs raw
        ok (raw,out)) = .ok (raw,out) ∧
      Canonical out ∧
      Decode out = Decode q + decodeWords (sumWords sums ⟨lane.val % 4,
        Nat.mod_lt _ (by omega)⟩) := by
  let limbs : Limbs32 := Array.make 4#usize [q.c0.a,q.c0.b,q.c1.a,q.c1.b]
  have hlimbs : state_only_poseidon.extension_limbs q = .ok limbs := by
    simpa [limbs] using RawPoseidonExtensionWords.extension_limbs_words q
  let laneFin : Fin 4 := ⟨lane.val % 4, Nat.mod_lt _ (by omega)⟩
  let inst := state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  let c : state_only_poseidon.external_linear_lazy.closure_1 := (limbs,sums,lane)
  have hcall : ∀ (i : Usize) (hi : i.val < 4), ∃ v : U64,
      inst.call_mut c i = .ok (v,c) ∧ column1Value q sums laneFin ⟨i.val,hi⟩ v := by
    intro i hi
    obtain ⟨v,hv,hvalue⟩ := external_column1_limb_call limbs sums lane i hlane hi hsums
    let j : Fin 4 := ⟨i.val,hi⟩
    have hword : (wordAt limbs i hi).val = qWords q j := by
      have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
      rcases hv with h0 | h1 | h2 | h3
      · simp [wordAt, qWords, limbs, Array.make, j, h0]
      · simp [wordAt, qWords, limbs, Array.make, j, h1]
      · simp [wordAt, qWords, limbs, Array.make, j, h2]
      · simp [wordAt, qWords, limbs, Array.make, j, h3]
    have hvalue' := hvalue
    rw [hword] at hvalue'
    have hvalue'' : v.val = qWords q j + sumWords sums laneFin j := by
      simpa [j, laneFin, sumWords, sumWordAt] using hvalue'
    refine ⟨v,hv,?_⟩
    exact hvalue''
  obtain ⟨raw,hcopy,hcells⟩ := AspisR1.PoseidonRaw4Constructor.source_success
      inst c (column1Value q sums laneFin) hcall
  have hraw : ∀ j : Fin 4,
      (AspisR1.RawPoseidonExtensionWords.limbAt raw j).val =
        qWords q j + sumWords sums laneFin j := by
    intro j
    have hj := hcells j
    change (raw.val[j.val]'(by simpa [raw.property] using j.isLt)).val = _ at hj
    exact hj
  obtain ⟨out,hdecodeRun,hcanonical,hmodel⟩ :=
    AspisR1.PoseidonExternalColumn1Reassembly.add_column_reassembly q sums laneFin raw hraw
  refine ⟨raw,out,?_ ,hcanonical,hmodel⟩
  simp [c, inst, hlimbs, hcopy, hdecodeRun, bind_tc_ok]

#print axioms source_success
end AspisR1.PoseidonExternalColumn1ArrayCall
