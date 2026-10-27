import XSa_ParserLane
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XSa_ClaimY1
open AspisR1ClaimPreparedBridge

theorem raw {H : Type} (sem : C.Sem H) (s : Slice U8) (n : Nat) :
 mapR cq (XRy_ClaimSelect.read (es sem) s 5 n) =
 (do let e ← XSa_ParserLane.field s n; ok e.c0) := by
 unfold XRy_ClaimSelect.read
 simp only [show ¬5<3 by omega,show ¬(5=3) by omega,show ¬(5=4) by omega,if_false]
 unfold XSa_ParserLane.field
 simp only [mapR_bind,bind_assoc_eq]
 apply congrArg (fun k => XRn_Join_sliceRange s (32*n) (32*n+32) >>= k)
 funext selected
 apply congrArg (fun k => _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes selected >>= k)
 funext opt
 cases opt <;> rfl

theorem sixth {S H : Type} (ops : AspisR1CurrentPreparedClaim.ClaimDotOps S)
 (sem : C.Sem H) (s : Slice U8) (n : Nat) (hn : n<29) :
 mapR (fun q => toClaimQ (cq q)) (XRy_ClaimSelect.read (es sem) s 5 n) =
 AspisR1CurrentPreparedClaim.ClaimScalar.read
   (AspisR1CurrentPreparedClaim.ClaimParser.withParser ops) (toClaimSem sem) s 5#usize (XRn_Join_usize n) := by
 have hcomp : mapR (fun q => toClaimQ (cq q)) (XRy_ClaimSelect.read (es sem) s 5 n) =
   mapR toClaimQ (mapR cq (XRy_ClaimSelect.read (es sem) s 5 n)) := by
   cases XRy_ClaimSelect.read (es sem) s 5 n <;> rfl
 rw [hcomp,raw]
 unfold AspisR1CurrentPreparedClaim.ClaimScalar.read
 have hp : ¬5#usize≤2#usize := by scalar_tac
 have hv : (5#usize).val=5 := by scalar_tac
 simp only [if_neg hp,hv,AspisR1CurrentPreparedClaim.ClaimParser.withParser]
 rw [←XSa_ParserLane.lane s n hn]
 simp only [mapR_bind,bind_map,bind_tc_ok]
 rfl

#print axioms raw
#print axioms sixth
end XSa_ClaimY1
