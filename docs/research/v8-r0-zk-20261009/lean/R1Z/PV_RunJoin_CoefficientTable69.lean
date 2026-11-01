import R1Z.PV_RunJoin_NativeBackendMatrix66
import R1Z.PV_RunJoin_NativePreparedArrays66
import R1Z.ProverCommitGammaCoefficients53
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientTable69
open Aeneas Aeneas.Std Result ProverRwFull
open PV_B2_F_ConstructorCarrier (amap)
open ProverRwDictionaryTower (fromW toW)
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)

theorem coefficient_row (c : Nat → Nat → Old.Q)
    (hc : ∀ l, l<29 → ∀ j, j<1024 → Canonical (c l j))
    (l j : Nat) (hl : l<29) (hj : j<1024) :
    ProverCommitGammaCoefficients53.coefficient c hc l j=c l (AspisR1.rowNat j) := by
  have h := (ProverCommitGammaCoefficients53.column_spec c hc ⟨l,hl⟩).2.2 ⟨j,hj⟩
  change decode (ProverCommitGammaCoefficients53.coefficient c hc l j)=
    decode (c l (AspisR1.rowEquiv.symm ⟨j,hj⟩).val) at h
  rw [← ProverCommitCoefficientModel51.row ⟨j,hj⟩] at h
  exact (AspisR1.ExtractedCurrentQM31Equality.decode_eq_iff _ _
    ((ProverCommitGammaCoefficients53.column_spec c hc ⟨l,hl⟩).2.1 j hj)
    (hc l hl _ (AspisR1.rowNat_lt j))).mp h

theorem table (c : Nat → Nat → Old.Q)
    (hc : ∀ l, l<29 → ∀ j, j<1024 → Canonical (c l j))
    (coeff : alloc.vec.Vec PV_RunJoin_CoefficientActualCell50.Column)
    (hlen : coeff.length=29)
    (hcoeff : coeff.val=(PV_RunJoin_BackendMatrix58.matrix
      (fun l j => fromW (ProverCommitNativeOps47.embedded (c l j)))).val.map
        PV_RunJoin_CoefficientActualCell50.permuted) :
    PV_RunJoin_GammaActualInputs50.table (alloc.vec.Vec.deref coeff) hlen=
      ProverCommitGammaCell53.table (ProverCommitGammaCoefficients53.wide c hc) := by
  apply Subtype.ext
  change coeff.val.map (amap toW)=_
  rw [hcoeff,List.map_map]
  change (List.ofFn (fun l : Fin 29 => ProverCommitArray49.array 1024#usize
    (fun j => fromW (ProverCommitNativeOps47.embedded (c l.val j))))).map _=_
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext l
  apply Subtype.ext
  change (PV_RunJoin_CoefficientActualCell50.permuted
    (ProverCommitArray49.array 1024#usize (fun j => fromW
      (ProverCommitNativeOps47.embedded (c l.val j))))).val.map toW=_
  simp only [PV_RunJoin_CoefficientActualCell50.permuted,ProverCommitArray49.array,
    List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [PV_RunJoin_ArrayEntries41.entries,ProverCommitArray49.array]
  rw [List.getElem?_eq_getElem (by rw [List.length_ofFn];exact AspisR1.rowNat_lt j.val)]
  simp only [Option.getD_some,List.getElem_ofFn,ProverRwDictionaryTower.w_inverse]
  rw [ProverCommitGammaCoefficients53.wide,coefficient_row c hc l.val j.val l.isLt j.isLt]
  rfl

#print axioms coefficient_row
#print axioms table
end R1Z.PV_RunJoin_CoefficientTable69
