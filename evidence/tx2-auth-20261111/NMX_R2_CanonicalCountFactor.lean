import NMX_R2_CanonicalBodyFactor
set_option autoImplicit false
namespace NMX_R2_CanonicalCountFactor
open RSL
/-- Seven actual index replies, in order, followed by the canonical body.
No child body or allocation is reduced. -/
theorem seven (L : PoolLib) (D : DeployedIds) (verifier pool : B32)
 (outputLane : UInt8) (slot : UInt64) (p m c l r e v : OwnedAccount) :
 NMX_R2_CB00.r001 L D verifier [p,m,c,l,r,e,v] pool outputLane slot =
 TX2_233.Ref L D ⟨verifier,[p,m,c,l,r,e,v],pool,outputLane,slot⟩ := by
 simp only [NMX_R2_CB00.r001,NMX_R2_CB00.r002,NMX_R2_CB00.r003,NMX_R2_CB00.r004,NMX_R2_CB00.r005,NMX_R2_CB00.r006,NMX_R2_CB00.r007,RS.index,RS.bind_pure]
 have h0 : [p,m,c,l,r,e,v][0]? = some p := by
  rw [List.getElem?_eq_getElem (by simp only [List.length_cons,List.length_nil]; omega)]
  rfl
 have h1 : [p,m,c,l,r,e,v][1]? = some m := by
  rw [List.getElem?_eq_getElem (by simp only [List.length_cons,List.length_nil]; omega)]
  rfl
 have h2 : [p,m,c,l,r,e,v][2]? = some c := by
  rw [List.getElem?_eq_getElem (by simp only [List.length_cons,List.length_nil]; omega)]
  rfl
 have h3 : [p,m,c,l,r,e,v][3]? = some l := by
  rw [List.getElem?_eq_getElem (by simp only [List.length_cons,List.length_nil]; omega)]
  rfl
 have h4 : [p,m,c,l,r,e,v][4]? = some r := by
  rw [List.getElem?_eq_getElem (by simp only [List.length_cons,List.length_nil]; omega)]
  rfl
 have h5 : [p,m,c,l,r,e,v][5]? = some e := by
  rw [List.getElem?_eq_getElem (by simp only [List.length_cons,List.length_nil]; omega)]
  rfl
 have h6 : [p,m,c,l,r,e,v][6]? = some v := by
  rw [List.getElem?_eq_getElem (by simp only [List.length_cons,List.length_nil]; omega)]
  rfl
 simp only [h0,h1,h2,h3,h4,h5,h6,RS.bind_pure]
 change NMX_R2_CB00.r008 L D verifier pool outputLane slot p m c l r e v =
  TX2_233.body L D ⟨verifier,[p,m,c,l,r,e,v],pool,outputLane,slot⟩ p m c l r e v
 exact NMX_R2_CanonicalBodyFactor.factor L D verifier pool outputLane slot p m c l r e v
#print axioms seven
end NMX_R2_CanonicalCountFactor
