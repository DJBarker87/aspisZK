import R1Z.PV_OWNI_BuildTotal
set_option autoImplicit false
namespace R1Z.PV_OWNI_Rows
open PV_OWNI_RawOps PV_OWNI_BuildTotal

theorem bounded (point : List Q) (width trailing suffix : Nat)
 (split:width+trailing=10) (hs:suffix<2^trailing) :
 ∀ entry∈entries point width trailing suffix,entry.1<1024 := by
 intro entry he
 obtain ⟨pref,hp,rfl⟩:=List.mem_map.mp he
 exact PV_RDB2D_SparseAddress.bound width trailing suffix pref split hs (List.mem_range.mp hp)

#print axioms bounded
end R1Z.PV_OWNI_Rows
