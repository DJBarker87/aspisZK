import R1Z.PV_CB_ProducerPost
set_option autoImplicit false
namespace R1Z.PV_CB_ProducerMake16
open Aeneas Aeneas.Std Result

theorem valid (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : U32)
    (h0 : PV_CB_CanonicalM31.Valid v0)
    (h1 : PV_CB_CanonicalM31.Valid v1)
    (h2 : PV_CB_CanonicalM31.Valid v2)
    (h3 : PV_CB_CanonicalM31.Valid v3)
    (h4 : PV_CB_CanonicalM31.Valid v4)
    (h5 : PV_CB_CanonicalM31.Valid v5)
    (h6 : PV_CB_CanonicalM31.Valid v6)
    (h7 : PV_CB_CanonicalM31.Valid v7)
    (h8 : PV_CB_CanonicalM31.Valid v8)
    (h9 : PV_CB_CanonicalM31.Valid v9)
    (h10 : PV_CB_CanonicalM31.Valid v10)
    (h11 : PV_CB_CanonicalM31.Valid v11)
    (h12 : PV_CB_CanonicalM31.Valid v12)
    (h13 : PV_CB_CanonicalM31.Valid v13)
    (h14 : PV_CB_CanonicalM31.Valid v14)
    (h15 : PV_CB_CanonicalM31.Valid v15)
    : PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid
      (Array.make 16#usize [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15]) := by
  intro word member
  change word ∈ [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms valid
end R1Z.PV_CB_ProducerMake16
