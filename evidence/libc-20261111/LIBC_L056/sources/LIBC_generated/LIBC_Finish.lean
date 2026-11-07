import LIBC_VStateCarriers
import NGC_FinishContents
import NJJ_Flush
set_option autoImplicit false
noncomputable section
namespace LIBC_Finish
open Aeneas Aeneas.Std Result AspisR1 RSL
abbrev Args := LIB_VCarriers.Weights × LIB_VCarriers.Acc
/-- The literal CLOSED175 invariant on this pending/accumulator pair. The
Prepared/range witnesses express own-input provenance, not a child Result. -/
def Domain (a : Args) : Prop := ∃ p start finish,
 NFS_QueryInvariant.Domain p start finish (LIBC_VStateCarriers.toAcc a.2) a.1
def value (a : Args) (_ : Env) : LIB_VCarriers.Acc :=
 {a.2 with weights := LIBC_VStateCarriers.mapVec LIBC_VStateCarriers.fromQ
  (⟨(NJJ_Flush.output a.1).val,(NJJ_Flush.output a.1).property⟩ : alloc.vec.Vec AspisR1Stage2.aspis_core.field.QM31)}
def child : Child Args LIB_VCarriers.Acc := LIB_Carriers.ofFn Domain value (fun _ _ => [])
theorem returns (a : Args) (env : Env) : NND_Returned.Returns (child.law a) env (value a env) :=
 LIB_Carriers.ofFn_returns _ _ _ a env
/-- Complete SAME destination flush, with every unmodified Acc field retained.
No returned flush, independently chosen output or allocator-success premise. -/
theorem source (a : Args) (env : Env) (domain : Domain a) :
 (do let out ← Port3_FlushInstall.flush a.1 (LIBC_VStateCarriers.toAcc a.2).weights.deref
     ok (LIBC_VStateCarriers.fromAcc
      {(LIBC_VStateCarriers.toAcc a.2) with weights := ⟨out.val,out.property⟩})) = ok (value a env) := by
 obtain ⟨p,start,finish,d⟩ := domain
 have raw : a.1.raw.val.length=64 := d.progress.2.1
 rw [NJJ_Flush.source _ _ raw d.width,bind_tc_ok]
 rfl
theorem frame (a : Args) (env : Env) :
 (value a env).rhs=a.2.rhs ∧ (value a env).power=a.2.power ∧ (value a env).next=a.2.next := ⟨rfl,rfl,rfl⟩
theorem weights_canonical (a : Args) (env : Env) :
 ∀ q∈(value a env).weights.val,Port3_FlushInstall.Canonical (LIBC_VStateCarriers.q q) := by
 intro q member
 change q ∈ (NJJ_Flush.output a.1).val.map LIBC_VStateCarriers.fromQ at member
 obtain ⟨native,hn,rfl⟩ := List.mem_map.mp member
 rw [LIBC_VStateCarriers.to_from_q]
 exact NJJ_Flush.canonical a.1 native hn
theorem graph (a : Args) (env : Env) (o : Obs LIB_VCarriers.Acc) :
 child.law a env o ↔ o = ⟨.ret (value a env),[]⟩ := Iff.rfl
#print axioms returns
#print axioms source
#print axioms frame
#print axioms weights_canonical
#print axioms graph
end LIBC_Finish
