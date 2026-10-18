import Aeneas
import PoseidonLeadingSourceDeclarationsV5
import PoseidonExternalPackedLoopModel
import PoseidonExternalPackedGroupCall
import PoseidonExternalPackedModel
import ExtractedMaskTowerAdd
import ExtractedMaskQM31Exact
import ExtractedMaskConstants
import RawPoseidonExternalRowReads
import AspisR1.PoseidonFullRoundCellStep
import ExtractedMaskQmPackBase4Arithmetic
import R0P.Poseidon

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result
namespace AspisR1.PoseidonExternalPackedSource
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep
open AspisR1.PoseidonExternalPackedLoopModel
open AspisR1.PoseidonExternalPackedGroupCall
open AspisR1.PoseidonExternalPackedModel
open AspisR1.ExtractedMaskTowerAdd
open AspisV8R15.ExactTowerBase (P)
open AspisR1.ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)

abbrev State := Array field.QM31 16#usize
abbrev Packed := Array field.QM31 4#usize
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

noncomputable def mapSumValue (sum : field.QM31) (hsum : CanonicalQM sum)
    (q : field.QM31) : field.QM31 := by
  letI : Decidable (CanonicalQM q) := Classical.propDecidable _
  exact if hq : CanonicalQM q then
    Classical.choose
      (AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q sum hq hsum)
  else field.QM31.ZERO

private theorem mapSumValue_spec (sum q : field.QM31)
    (hsum : CanonicalQM sum) (hq : CanonicalQM q) :
    field.QM31.add q sum = .ok (mapSumValue sum hsum q) ∧
    CanonicalQM (mapSumValue sum hsum q) ∧
    Decode (mapSumValue sum hsum q) = Decode q + Decode sum := by
  have hspec := Classical.choose_spec
    (AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q sum hq hsum)
  have hvalue : mapSumValue sum hsum q =
      Classical.choose
        (AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q sum hq hsum) := by
    simp [mapSumValue,hq]
  simpa [hvalue] using hspec

private theorem mapState_sum_success (xs : List field.QM31) (sum : field.QM31)
    (hsum : CanonicalQM sum) (hxs : ∀ q ∈ xs, CanonicalQM q) :
    AspisV8R19.TraversalRuntime.mapState
      state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31.call_mut
      xs sum = .ok (xs.map (mapSumValue sum hsum),sum) := by
  induction xs with
  | nil => rfl
  | cons q xs ih =>
      have hq : CanonicalQM q := hxs q (by simp)
      have hcall :
          state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31.call_mut
            sum q = .ok (mapSumValue sum hsum q,sum) := by
        obtain ⟨hadd,_,_⟩ := mapSumValue_spec sum q hsum hq
        unfold state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31.call_mut
        simp only [hadd,bind_tc_ok]
      have htail : ∀ x ∈ xs, CanonicalQM x := by
        intro x hx
        exact hxs x (by simp [hx])
      simp only [AspisV8R19.TraversalRuntime.mapState,hcall,bind_tc_ok,
        ih htail, List.map_cons] <;> rfl

noncomputable def mappedPacked (sum : field.QM31) (hsum : CanonicalQM sum)
    (packed : Packed) : Packed :=
  ⟨packed.val.map (mapSumValue sum hsum), by simpa [packed.property]⟩

private theorem map_sum_success (packed : Packed) (sum : field.QM31)
    (hpacked : packedCanonical packed) (hsum : CanonicalQM sum) :
    ∃ out : Packed,
      core.array.Array.map
        state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31
        packed sum = .ok out ∧ packedCanonical out ∧
      ∀ j : Fin 4,
        Decode (packedCell out j) = Decode (packedCell packed j) + Decode sum := by
  have hxs : ∀ q ∈ packed.val, CanonicalQM q := by
    intro q hq
    obtain ⟨j,hj⟩ := List.mem_iff_getElem.mp hq
    have hjlt : j < 4 := by simpa [packed.property] using hj.1
    have hcan := hpacked ⟨j,hjlt⟩
    simpa [packedCell,hj.2] using hcan
  have hstate := mapState_sum_success packed.val sum hsum hxs
  let out : Packed := mappedPacked sum hsum packed
  have hmap : core.array.Array.map
      state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31
      packed sum = .ok out := by
    have hmap' := Aeneas.Std.core.array.Array.map_success
      state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31
      packed sum (packed.val.map (mapSumValue sum hsum)) sum hstate
    simpa [out,mappedPacked] using hmap'
  refine ⟨out,hmap,?_,?_⟩
  · intro j
    have hq := hpacked j
    have hvalue := mapSumValue_spec sum (packedCell packed j) hsum hq
    simpa [packedCanonical,packedCell,out,mappedPacked] using hvalue.2.1
  · intro j
    have hq := hpacked j
    have hvalue := mapSumValue_spec sum (packedCell packed j) hsum hq
    simpa [packedCell,out,mappedPacked] using hvalue.2.2

private theorem packed_read (packed : Packed) (index : Usize) (j : Fin 4)
    (hindex : index.val = j.val) :
    Array.index_usize packed index = .ok (packedCell packed j) := by
  have hb : index.val < packed.val.length := by
    rw [hindex]
    simpa [packed.property] using j.isLt
  have hread := AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok packed index
    (by simpa [packed.property] using hb)
  have heq : (⟨index.val,by simpa [packed.property] using hb⟩ : Fin 4) = j := by
    apply Fin.ext
    exact hindex
  change Array.index_usize packed index =
    .ok (cell packed (⟨index.val,by simpa [packed.property] using hb⟩ : Fin 4)) at hread
  rw [heq] at hread
  exact hread

private theorem ordered_add_success (packed : Packed) (hpacked : packedCanonical packed) :
    ∃ q0 q1 q2 q3 s : field.QM31,
      (do
        let x0 ← Array.index_usize packed 0#usize
        let x1 ← field.QM31.add field.QM31.ZERO x0
        let x2 ← Array.index_usize packed 1#usize
        let x3 ← field.QM31.add x1 x2
        let x4 ← Array.index_usize packed 2#usize
        let x5 ← field.QM31.add x3 x4
        let x6 ← Array.index_usize packed 3#usize
        field.QM31.add x5 x6) = .ok s ∧
      CanonicalQM s ∧
      Decode s = (((0 + Decode (packedCell packed 0)) + Decode (packedCell packed 1)) +
          Decode (packedCell packed 2)) + Decode (packedCell packed 3) := by
  have h0 := packed_read packed 0#usize 0 (by simp [UScalar.ofNatCore_val_eq])
  have h1 := packed_read packed 1#usize 1 (by simp [UScalar.ofNatCore_val_eq])
  have h2 := packed_read packed 2#usize 2 (by simp [UScalar.ofNatCore_val_eq])
  have h3 := packed_read packed 3#usize 3 (by simp [UScalar.ofNatCore_val_eq])
  have hz := AspisR1.ExtractedMaskConstants.zero_canonical
  obtain ⟨q1,hadd1,hcan1,hdec1⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact
      field.QM31.ZERO (packedCell packed 0) hz (hpacked 0)
  obtain ⟨q3,hadd2,hcan3,hdec3⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q1 (packedCell packed 1)
      hcan1 (hpacked 1)
  obtain ⟨q5,hadd3,hcan5,hdec5⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q3 (packedCell packed 2)
      hcan3 (hpacked 2)
  obtain ⟨s,hadd4,hcanS,hdecS⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q5 (packedCell packed 3)
      hcan5 (hpacked 3)
  change Decode q1 = Decode field.QM31.ZERO + Decode (packedCell packed 0) at hdec1
  change Decode q3 = Decode q1 + Decode (packedCell packed 1) at hdec3
  change Decode q5 = Decode q3 + Decode (packedCell packed 2) at hdec5
  have hzDecode : Decode field.QM31.ZERO = 0 := AspisR1.ExtractedMaskConstants.zero_decode
  refine ⟨packedCell packed 0,q1,packedCell packed 1,q3, s, ?_, hcanS, ?_⟩
  · simp only [h0,bind_tc_ok,hadd1,bind_tc_ok,h1,bind_tc_ok,hadd2,bind_tc_ok,
      h2,bind_tc_ok,hadd3,bind_tc_ok,h3,bind_tc_ok,hadd4]
  · calc
      Decode s = Decode q5 + Decode (packedCell packed 3) := hdecS
      _ = (((Decode field.QM31.ZERO + Decode (packedCell packed 0)) +
            Decode (packedCell packed 1)) + Decode (packedCell packed 2)) +
            Decode (packedCell packed 3) := by
        rw [hdec5,hdec3,hdec1]
      _ = (((0 + Decode (packedCell packed 0)) + Decode (packedCell packed 1)) +
            Decode (packedCell packed 2)) + Decode (packedCell packed 3) := by
        rw [hzDecode]

theorem external_linear_packed_source_success (state : State)
    (hstate : CanonicalState state) :
    ∃ out : Packed,
      state_only_poseidon.external_linear_packed state = .ok out ∧
      packedCanonical out ∧
      ∀ group column : Fin 4,
        Decode (packedCell out group) =
          R0P.poseidonPackingFormula iBasis uBasis
            (fun j => R0P.poseidonExternalLinear
              (fun i : Fin 16 => Decode (cell state i))
              (AspisR1.PoseidonExternalPackedModel.lane group j)) := by
  let initial : Packed := Array.repeat 4#usize field.QM31.ZERO
  obtain ⟨localPacked,hloop,hlocalCan,hlocalModel⟩ :=
    loop_source_success state hstate
  obtain ⟨q0,q1,q2,q3,sum,haddRun,hcanSum,hsumModel⟩ :=
    ordered_add_success localPacked hlocalCan
  obtain ⟨out,hmap,houtCan,houtModel⟩ :=
    map_sum_success localPacked sum hlocalCan hcanSum
  have hsource : state_only_poseidon.external_linear_packed state = .ok out := by
    have htail := congrArg
      (fun run : Result field.QM31 => do
        let s ← run
        core.array.Array.map
          state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31
          localPacked s) haddRun
    simp only [bind_tc_ok, hmap] at htail
    simp only [bind_assoc_eq] at htail
    unfold state_only_poseidon.external_linear_packed
    simp only [hloop, bind_tc_ok]
    exact htail
  refine ⟨out,hsource,houtCan,?_⟩
  intro group column
  have hmodel := AspisR1.PoseidonExternalPackedModel.packed_external_eq
    (fun i : Fin 16 => Decode (cell state i)) iBasis uBasis group
  have hlocal : ∀ g : Fin 4, Decode (packedCell localPacked g) =
      AspisR1.PoseidonExternalPackedModel.localPacked
        (fun i : Fin 16 => Decode (cell state i)) iBasis uBasis g := by
    intro g
    have hrunModel := hlocalModel g
    change Decode (packedCell localPacked g) = packedModel state g at hrunModel
    have hpacking : AspisR1.PoseidonExternalPackedModel.localPacked
        (fun i : Fin 16 => Decode (cell state i)) iBasis uBasis g =
        packedModel state g := by
      change R0P.poseidonPackingFormula iBasis uBasis
          (AspisR1.PoseidonExternalPackedModel.localCell
            (fun i : Fin 16 => Decode (cell state i)) g) =
        R0P.poseidonPackingFormula iBasis uBasis
          (R0P.poseidonMat4 (fun r => Decode (cell state (lane g r))))
      apply congrArg (R0P.poseidonPackingFormula iBasis uBasis)
      funext column
      rfl
    exact hrunModel.trans hpacking.symm
  have hgroup := hlocal group
  have hsum : Decode sum =
      ((((0 + AspisR1.PoseidonExternalPackedModel.localPacked
        (fun i : Fin 16 => Decode (cell state i)) iBasis uBasis 0) +
        AspisR1.PoseidonExternalPackedModel.localPacked
          (fun i : Fin 16 => Decode (cell state i)) iBasis uBasis 1) +
        AspisR1.PoseidonExternalPackedModel.localPacked
          (fun i : Fin 16 => Decode (cell state i)) iBasis uBasis 2) +
        AspisR1.PoseidonExternalPackedModel.localPacked
          (fun i : Fin 16 => Decode (cell state i)) iBasis uBasis 3) := by
    rw [hsumModel]
    simp only [hlocal]
  have houtj := houtModel group
  rw [hgroup,hsum] at houtj
  rw [hmodel]
  -- `packed_external_eq` states the precise source-order total used by
  -- `ordered_add_success`; the final output adds that total to each local
  -- group pack.
  exact houtj

#print axioms map_sum_success
#print axioms ordered_add_success
#print axioms external_linear_packed_source_success
end AspisR1.PoseidonExternalPackedSource
