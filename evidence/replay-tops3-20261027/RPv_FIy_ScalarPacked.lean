import RPv_FIy_ListDecoded
import RPv_FIw_ScalarSuffix
import RPv_FIx_PreweightedMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_ScalarPacked
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FIw_ScalarSuffix (Public Openings Selectors)

def model (p : Public) (o : Openings) (s : Selectors) (i : Fin (2#usize).val) : K :=
  ((FIw_ScalarSuffix.model p o s)[i.val]?).getD 0

theorem value (p : Public) (o : Openings) (s : Selectors) (packed out : Array NQ 24#usize)
    (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low) (hp : canonical packed)
    (hb : p.asset_id.val<FIw_ScalarArithmetic.P)
    (ha : (p.withdrawal_amount.getD 0#u32).val<FIw_ScalarArithmetic.P)
    (success : FIw_ScalarSuffix.run p o s packed=ok out) :
    canonical out ∧ ∀ j : Fin (24#usize).val,
      decoded out j=decoded packed j+FIx_SelectedMeaning.contribution (model p o s) 92 j.val := by
  obtain ⟨scalars,hr,hc,hv⟩ := FIw_ScalarSuffix.value_exact p o s packed out hz hh hl hb ha success
  have same : decoded scalars=model p o s := funext (FIy_ListDecoded.value scalars _ hv)
  exact FIx_PreweightedMeaning.value packed out 92#usize scalars (model p o s) same
    (by decide) (by decide) hp hc hr
#print axioms value
end AspisR1.FIy_ScalarPacked
end
