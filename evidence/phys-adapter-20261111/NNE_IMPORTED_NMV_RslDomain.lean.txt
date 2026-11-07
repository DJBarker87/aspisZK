import NMV_RslSnapshots
set_option autoImplicit false
namespace NMV_RslDomain
open RSL NMV_RslLaws NMV_RslSnapshots

/-- (D1) is produced by the seven snapshots. (D2) is transported from the
entry payloads at the SAME account indices. This lemma is parametric in V. -/
theorem domain241 (V : TX2_241.V2Lib) (a : TX2_240.Args) (s : SdkState)
 (xs : List OwnedAccount) (slot : Except ProgramError UInt64)
 (h7 : a.accounts.length=7) (images : Images s a.accounts TX2_240.snapLens xs)
 (dom : TX2_240.Domain V a s) :
 TX2_241.Domain V ⟨a.program_id,xs,a.data,slot⟩ := by
 constructor
 · exact images_consistent s _ _ _ images
 · intro x0 x6 ck pr _ h0 h6 hck hpr hlen
   obtain ⟨a0,l0,ha0,hl0,im0⟩ := images_lookup s _ _ _ images 0 x0 h0
   obtain ⟨a6,l6,ha6,hl6,im6⟩ := images_lookup s _ _ _ images 6 x6 h6
   have eq6 : l6=(CHECKPOINT_BYTES,CHECKPOINT_BYTES) := by
     simpa only [TX2_240.snapLens,List.getElem?_cons_succ,List.getElem?_cons_zero,
       Option.some.injEq] using hl6.symm
   have ck_origin := im6.origin ck hck
   have pr_origin := im0.origin pr hpr
   have cklen : ck.length=CHECKPOINT_BYTES := by
     have hh := im6.extent ck hck
     rw [eq6] at hh
     exact hh.elim id id
   have root := dom a0 a6 h7 ha0 ha6 (ck_origin ▸ cklen) (pr_origin ▸ hlen)
   simpa only [←ck_origin,←pr_origin] using root

#print axioms domain241
end NMV_RslDomain
