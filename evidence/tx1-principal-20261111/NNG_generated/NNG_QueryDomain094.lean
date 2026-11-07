import NNG_GeometryFacts094
import NNG_PendingDomain094
import NNG_PreparedFacts094
import LIBC_QueryLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_QueryDomain094
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- Canonical alpha transport is limbwise and symbolic. -/
theorem alpha (p : LIB_VCarriers.Prepared)
 (canonical : ∀ x∈p.alpha.val,NFN_LPi_FieldValues.canonE (NFW_SampledDomains.toNative x)) (j : Fin 2) :
 Port4C_QueryArithmetic.CanonE
  ((NFW_PreparedPort.prepared p).alpha.val[j.val]'(by rw [(NFW_PreparedPort.prepared p).alpha.property];exact j.isLt)) := by
 have bound : j.val<p.alpha.val.length := by rw [p.alpha.property];exact j.isLt
 have h := canonical _ (List.getElem_mem bound)
 simp only [NFW_PreparedPort.prepared,NFW_PreparedPort.map,List.getElem_map]
 exact ⟨⟨h.1.1.1,h.1.1.2,h.1.2.1,h.1.2.2⟩,⟨h.2.1.1,h.2.1.2,h.2.2.1,h.2.2.2⟩⟩
#print axioms alpha

/-- Every original CLOSED088 input clause is derived from the SAME preceding
successful preparation, initializer, geometry and pending calls. -/
theorem reached (proof : RSL.Bytes) (width : proof.length=57607)
 (input : LIBC_PreparedLaw.Args) (env : RSL.Env) (p : LIB_VCarriers.Prepared) (g : LIB_VCarriers.E29)
 (a : LIB_VCarriers.Acc) (geo : LIB_VCarriers.Geo) (pending : LIB_VCarriers.Weights)
 (ep ea eg eb : List RSL.Event)
 (prepared : LIBC_PreparedLaw.law input env ⟨.ret (.ok p,g),ep⟩)
 (initial : LIBC_AccNew.child.run () env ⟨.ret (.ok a),ea⟩)
 (geometry : LIBC_Geometry.child.run (p,0,10) env ⟨.ret (.ok geo),eg⟩)
 (weights : LIBC_WeightsNew.child.run a env ⟨.ret (.ok pending),eb⟩) :
 LIBC_QueryLoop.Domain (proof,p,a,g,geo,pending,10) := by
 have fields := NNG_PreparedFacts094.canonical input env p g ep prepared
 have start := NNG_PendingDomain094.initial env a pending ea eb (NFW_PreparedPort.prepared p)
  initial weights fields.2.2.2.1
 have geom := NNG_GeometryFacts094.returned p env geo eg geometry
 refine ⟨rfl,start.2,?_⟩
 change NFS_PacketRoot.Domain (LIBC_Bytes.raw proof) (NFW_PreparedPort.prepared p)
  (NFW_PreparedPort.map NFW_PreparedPort.e g) geo 0 10#usize (LIBC_VStateCarriers.toAcc a) pending
 refine ⟨?_,Or.inl rfl,by decide,start.1,fields.2.2.2.2,
  alpha p fields.2.2.1 ⟨0,by decide⟩,alpha p fields.2.2.1 ⟨1,by decide⟩,?_,?_,?_,geom.2.2.2.1,geom.2.2.2.2⟩
 · have bound : proof.length≤Usize.max := by rw [width];scalar_tac
   exact (LIBC_Bytes.raw_length proof bound).trans width
 · exact congrArg UScalar.val geom.1
 · rw [geom.1]
   exact geom.2.1
 · rw [geom.1]
   exact geom.2.2.1
#print axioms reached
end AspisR1.NNG_QueryDomain094
