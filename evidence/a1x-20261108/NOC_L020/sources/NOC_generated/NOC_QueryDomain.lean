import NNG_QueryDomain094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_QueryDomain
open Aeneas Aeneas.Std Result

/-- A returned non-fallback result-graph value is a returned observation of
its own law, at its own (empty or logged) events. -/
theorem graphRet {A B : Type} (f : A → B) (fb b : B) (m : Result A) (ev : List RSL.Event)
 (h : LIBC_ResultGraph.value f fb m = b) (hne : fb ≠ b) :
 LIB_Carriers.resultObs f ev m = ⟨.ret b,ev⟩ := by
 cases m with
 | ok x => simp only [LIBC_ResultGraph.value] at h; subst h; rfl
 | fail e => simp only [LIBC_ResultGraph.value] at h; exact absurd h hne
 | div => simp only [LIBC_ResultGraph.value] at h; exact absurd h hne

theorem prepared (input : LIBC_PreparedLaw.Args) (env : RSL.Env) (p : LIB_VCarriers.Prepared)
 (g : LIB_VCarriers.E29) (h : LIBC_PreparedLaw.value input env = (.ok p,g)) :
 LIBC_PreparedLaw.law input env ⟨.ret (.ok p,g),LIBC_PreparedLog.events (LIBC_PreparedLaw.run input env).1⟩ := by
 unfold LIBC_PreparedLaw.value at h
 cases hr : (LIBC_PreparedLaw.run input env).2 with
 | ok native =>
  rw [hr] at h
  exact (LIBC_PreparedLaw.returned input env _ _).mpr ⟨native,hr,h.symm,rfl⟩
 | fail e => rw [hr] at h; simp at h
 | div => rw [hr] at h; simp at h

/-- X2: the caller Domain of the 094 query loop (LIBC_QueryLoop.Domain, whose
third clause is NFS_PacketRoot.Domain) from the SAME returned prepare,
accumulator, geometry and pending values. -/
theorem domain (input : LIBC_PreparedLaw.Args) (proof : RSL.Bytes) (width : proof.length = 57607)
 (env : RSL.Env) (p : LIB_VCarriers.Prepared) (g : LIB_VCarriers.E29)
 (a : LIB_VCarriers.Acc) (geo : LIB_VCarriers.Geo) (pending : LIB_VCarriers.Weights)
 (hp : LIBC_PreparedLaw.value input env = (.ok p,g))
 (ha : LIB_VLib.accNewValue () env = .ok a)
 (hg : LIB_VLib.geometryValue (p,0,10) env = .ok geo)
 (hb : LIB_VLib.weightsNewValue a env = .ok pending) :
 LIBC_QueryLoop.Domain (proof,p,a,g,geo,pending,10) := by
 have initial : LIBC_AccNew.child.law () env ⟨.ret (.ok a),[]⟩ :=
  (graphRet _ _ _ _ [] ha (by intro h; cases h)).symm
 have geometry : LIBC_Geometry.child.law (p,0,10) env ⟨.ret (.ok geo),[]⟩ :=
  Or.inl (graphRet _ _ _ _ [] hg (by intro h; cases h)).symm
 have weights : LIBC_WeightsNew.child.law a env ⟨.ret (.ok pending),[]⟩ :=
  (graphRet _ _ _ _ [] hb (by intro h; cases h)).symm
 exact NNG_QueryDomain094.reached proof width input env p g a geo pending _ [] [] []
  (prepared input env p g hp) initial geometry weights
#print axioms graphRet
#print axioms prepared
#print axioms domain
end AspisR1.NOC_QueryDomain
end
