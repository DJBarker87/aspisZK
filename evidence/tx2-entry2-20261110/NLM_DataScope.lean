import NLM_ReadCalls
import NGL_StorageCases
set_option autoImplicit false
noncomputable section
namespace NLM_DataScope
open Aeneas Aeneas.Std Result
abbrev Owned := AdapterRw.r1_pool_adapter.owned.OwnedAccount
/-- Every decoder-admitted snapshot success has a positive bounded length. -/
theorem allowed_positive (n : Usize) (allowed : NGL_StorageCases.Allowed n) : 0<n.val := by
 simp only [NGL_StorageCases.Allowed,List.mem_cons,List.not_mem_nil,or_false] at allowed
 rcases allowed with h|h|h|h|h|h|h|h|h <;> omega
/-- This domain comes from the actual data() return on the SAME stored
snapshot. It is a local entered-call consequence, never a free root bound. -/
theorem data_window (ops : AdapterRw.Ops) (a : Owned) (valid : NGL_StorageCases.Domain a)
 (bytes : Slice U8)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
    (NGL_CloneDomain.install ops) a=.ok (.Ok bytes)) :
 0<bytes.val.length ∧ bytes.val.length≤58295 := by
 rw [NGL_CloneDomain.data_result] at read
 rcases valid.1 with ⟨hl,hb⟩ | ⟨n,hl,hb⟩ | ⟨n,v,hl,hb,hlen,hbound⟩
 · rw [hb] at read; cases read
 · rw [hb] at read; cases read
 · rw [hb] at read
   cases read
   have allowed := valid.2 n v hl hb
   exact ⟨by rw [←hlen]; exact allowed_positive n allowed,by rw [←hlen]; exact hbound⟩
#print allowed_positive
#print data_window
#print axioms allowed_positive
#print axioms data_window
end NLM_DataScope
