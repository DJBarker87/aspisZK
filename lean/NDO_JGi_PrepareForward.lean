import NDO_JGi_PrepareReturn
import RPz7_PAln_OpeningStages
set_option autoImplicit false
namespace AspisR1.JGi_PrepareForward
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem checked_add {ty : UScalarTy} (a b c : UScalar ty) (value : c.val=a.val+b.val) :
    (a+b : Result (UScalar ty))=ok c := by
  obtain ⟨out,call,meaning⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=a) (y:=b) (by scalar_tac))
  have same : out=c := by scalar_tac
  exact same ▸ call
#print axioms checked_add

/-- Constructor direction for the existing full two-fold preparation spine.
This is a generic control lemma; the concrete claim call remains a separate
forward obligation until instantiated on the retained bytes. -/
theorem source {Hash : Type} (B : PreparedScratchModel.Boundaries) (D : aspis_core.Digest32 Hash)
    (sem : r1_semantic.Verified Hash) (view : verifier.View) (hash : Hash)
    (out : verifier.Prepared) (scratch input : Array aspis_core.field.WideExact 29#usize)
    (variant : view.variant=.S2)
    (calls : PAln_OpeningStages.Double B D sem view hash out scratch) :
    PreparedScratchModel.prepare B D sem view hash input=ok (.Ok out,scratch) := by
  obtain ⟨t0,t1,t2,t3,t4,t5,t6,inactive,root,bytes1,bytes2,gamma,kappa,a0,a1,rho,queries,claim,
    seed,gammaCall,serialize,kappaCall,a0Call,rootCall,first,second,a1Call,query,rhoCall,powers,claimed,output⟩ := calls
  subst out
  unfold PreparedScratchModel.prepare
  rw [r1_wire.SemanticTranscript.impl.state,bind_tc_ok,seed,bind_tc_ok]
  rw [gammaCall,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [serialize,bind_tc_ok]
  try simp only [lift,bind_tc_ok]
  rw [kappaCall,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [a0Call,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [variant]
  have folds : transport.Variant.folds transport.Variant.S2=ok 2#usize := by
    simp [transport.Variant.folds,transport.Variant.Insts.CoreCmpPartialEqVariant.eq,read_discriminant,transport.Variant.read_discriminant]
  rw [folds,bind_tc_ok,if_pos rfl]
  have add : (32#usize+224#usize : Result Usize)=ok 256#usize := checked_add _ _ _ (by scalar_tac)
  try simp only [ite_true]
  rw [add,bind_tc_ok,rootCall,bind_tc_ok]
  try simp only [lift,bind_tc_ok]
  rw [first,bind_tc_ok,second,bind_tc_ok,a1Call,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [query,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  have addRow : (31#u8+1#u8 : Result U8)=ok 32#u8 := checked_add _ _ _ (by scalar_tac)
  rw [addRow,bind_tc_ok]
  try simp only [lift,bind_tc_ok]
  erw [rhoCall,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [powers,bind_tc_ok,claimed,bind_tc_ok]
  exact JGi_PrepareReturn.source sem view gamma kappa a0 a1 claim rho queries t6 scratch variant
#print axioms source
end AspisR1.JGi_PrepareForward
