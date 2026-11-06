import NIS_Distinct3
import NLD_Stage1Source
import NLQ_Route
set_option autoImplicit false
noncomputable section
namespace NLQ_EmissionGuard
open Aeneas Aeneas.Std Result AspisR1
/-- Only the concrete U8 specialization is consumed below. The slot is
heterogeneous; HEq keeps this installation well-typed at its generic type. -/
def equality (ops : AdapterRw.Ops) : AdapterRw.Ops :=
 {ops with op1 := fun _ d a => by classical exact ok (decide (HEq d.val a.val))}
def installed (ops : AdapterRw.Ops) := NGL_ReadonlyModel.install (equality ops)
def accounts (a b c : NIS_Distinct3.A) : Slice NIS_Distinct3.A :=
 ⟨[a,b,c],by simp; scalar_tac⟩
/-- Corrected claim: the complete emitted eleven branch reaches the actual
three-account distinct helper and retains its first InvalidArgument error. -/
theorem eleven_duplicate (ops : AdapterRw.Ops) (p : AdapterRw.solana_pubkey.Pubkey)
 (a b c : NIS_Distinct3.A) (same : a.key=b.key) :
 AdapterRw.r1_pool_adapter.owned.stage1_owned (installed ops) p (accounts a b c) NJD_Prefixes.eleven =
 .ok (.Err .InvalidArgument) := by
 have h10 : (installed ops).op1 core.cmp.PartialEqU8 NJD_Prefixes.eleven
   (Array.make 2#usize [3#u8,10#u8]) = .ok false := by
   simp [installed,equality,NGL_ReadonlyModel.install,NJD_Prefixes.eleven,Array.make]
 have h11 : (installed ops).op1 core.cmp.PartialEqU8 NJD_Prefixes.eleven
   (Array.make 2#usize [3#u8,11#u8]) = .ok true := by
   simp [installed,equality,NGL_ReadonlyModel.install,NJD_Prefixes.eleven,Array.make]
 have len : Slice.len (accounts a b c) = 3#usize := rfl
 have ix0 : Slice.index_usize (accounts a b c) 0#usize = .ok a := rfl
 have ix1 : Slice.index_usize (accounts a b c) 1#usize = .ok b := rfl
 have ix2 : Slice.index_usize (accounts a b c) 2#usize = .ok c := rfl
 have hd : AdapterRw.r1_pool_adapter.owned.require_distinct_accounts (installed ops)
   (Array.make 3#usize [a,b,c]) = .ok (.Err .InvalidArgument) := by
   change AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
     (NGL_ReadonlyModel.install (equality ops)) (NIS_Distinct3.array a b c) = _
   rw [NIS_Distinct3.source]
   simp [same]
 unfold AdapterRw.r1_pool_adapter.owned.stage1_owned
 simp only [h10,h11,bind_tc_ok,Bool.false_eq_true,ite_false,ite_true,len,ne_eq,not_true_eq_false]
 simp only [ix0,ix1,ix2,bind_tc_ok,hd]
 rfl
#check @eleven_duplicate
#print axioms eleven_duplicate
end NLQ_EmissionGuard
