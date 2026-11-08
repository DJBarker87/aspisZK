import NNX_Mask10
import NNV_FinishTerminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_Masked
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

theorem extra (e : K29) :
 Array.index_usize (k29Raw e) 28#usize = .ok (LIB_VScalarCarriers.toRaw (at28 e)) := by
 rw [NNX_ArrayRead.source _ _ (by rw [(k29Raw e).property];decide)]
 congr 1
 simp only [k29Raw,LIB_VScalarCarriers.array,List.getElem_map,at28]
 rfl

theorem source (c : Claims) (alpha : Alpha) (eta terminal : QM31) (e : K29) :
 (do let mask ← FIp_SemanticArithmetic.mask (LIB_VField.c1 c) (LIB_VField.maskOnly c)
       (LIB_VField.g c) (alphaRaw alpha)
     let product ← FIp_SemanticArithmetic.mul (LIB_VScalarCarriers.toRaw eta) (LIB_VScalarCarriers.toRaw terminal)
     let sum ← FIp_SemanticArithmetic.add mask product
     let last ← Array.index_usize (k29Raw e) 28#usize
     FIp_SemanticArithmetic.add sum last) =
 .ok (LIB_VScalarCarriers.toRaw
  (LIB_VField.qadd (LIB_VField.qadd (LIB_VField.maskValue c alpha) (LIB_VField.qmul eta terminal)) (at28 e))) := by
 rw [LIB_VField.mask_exact,bind_tc_ok,LIB_VField.qmul_exact,bind_tc_ok,
  LIB_VField.qadd_exact,bind_tc_ok,extra,bind_tc_ok,LIB_VField.qadd_exact]
#print axioms extra
#print axioms source
end AspisR1.NNX_Masked
end
