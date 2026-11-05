import NHT_Tx2CommonModel
import NFW_QueryResume
import NGM_FinishDomain
set_option autoImplicit false
noncomputable section
namespace NHT_PacketOps
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
abbrev TopOps := VTop_Stages.Ops
abbrev QueryOps := Port3_NativeQueryBody.Ops

/-- Native powers packet with the existing nominal coordinate port. -/
def powers (N : Usize) (gamma : aspis_core.field.wide_exact.WideExact) := do
 let out ← FIo_Native.weights.powers N (FIo_Install.toE gamma)
 ok (FIp_DotsAdapter.fromArray out)

/-- The CLOSED NFS TX2 twelve-step model. Consumer domains are supplied at
query_source below; this definition alone asserts no native call association. -/
def query (base : QueryOps) (qPlace gPlace : Nat) (proof : Slice U8)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (_obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (finish : Usize) :=
 NFG_QueryLoopDefs.run
  (NFS_QueryLoopRoot.child base proof p g geometry qPlace gPlace)
  finish 12 (.Ok (a,pending))

/-- OPEN members stay named in base: resume, finish, parse/inactive, root,
Merkle, geometry, pending initializer and their exact native installations. -/
def installed (base : TopOps) (qbase : QueryOps) (qPlace gPlace : Nat) : TopOps :=
 {NHT_Tx2CommonModel.constants base with
   op17 := powers
   op6 := query qbase qPlace gPlace
   op9 := Port3_FlushInstall.flush}

theorem source (base : TopOps) (qbase : QueryOps) (qPlace gPlace : Nat)
 {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
 (pub proof checkpoint : Slice U8) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) :
 NHT_EmittedCommon.tx2_common (installed base qbase qPlace gPlace)
   D pub proof checkpoint hash obs =
 VTop_Stages.verifier.candidate.tx2_common (installed base qbase qPlace gPlace)
   D pub proof checkpoint hash obs := by
 exact NHT_Tx2CommonModel.source {base with op17:=powers,
  op6:=query qbase qPlace gPlace,op9:=Port3_FlushInstall.flush}
  D pub proof checkpoint hash obs

theorem powers_reply (N : Usize) (gamma : aspis_core.field.wide_exact.WideExact)
 (out : Array FIo_Install.NE N)
 (native : FIo_Native.weights.powers N (FIo_Install.toE gamma)=ok out) :
 powers N gamma=ok (FIp_DotsAdapter.fromArray out) := by
 unfold powers
 rw [native]
 rfl

/-- Exact domain and SAME resumed pending from NFW; release observer is None. -/
theorem query_source (base : QueryOps) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (width : a.weights.val.length=64)
 (weights : NFS_NEV_WeightDomains.Canonical (NEV_AccumulateCarriers.fromAccumulator a).weights)
 (rhs : NBO_TailDomain.WideCanonical a.rhs) (power : NBF_PowerStep.Canonical a.power)
 (rho : NBF_PowerStep.Canonical p.rho) (start : a.next.val=10)
 (gamma : NFN_LPi_FieldValues.NE) (canonicalGamma : NFN_LPi_FieldValues.canonE gamma)
 (g : Array NFN_LPi_FieldValues.NE 29#usize)
 (powers : FIo_Native.weights.powers 29#usize gamma=ok g)
 (geometry : verifier.QueryGeometry) (qPlace gPlace : Nat) :
 query base qPlace gPlace proof p a (FIp_DotsAdapter.fromArray g) none geometry
   (NFW_QueryResume.pending a) 22#usize =
 Port3_NativeQueryBody.verifier.candidate.query_loop (NFS_QueryOps.installed base)
   proof p a (FIp_DotsAdapter.fromArray g) none geometry (NFW_QueryResume.pending a) 22#usize :=
 NFW_QueryResume.tx2 base proof p a width weights rhs power rho start
  gamma canonicalGamma g powers geometry qPlace gPlace
#print axioms source
#print axioms powers_reply
#print axioms query_source
end NHT_PacketOps
