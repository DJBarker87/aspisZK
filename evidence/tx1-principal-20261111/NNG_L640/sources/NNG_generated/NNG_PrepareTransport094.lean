import NNG_PrepareAdapter094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PrepareTransport094
open Aeneas Aeneas.Std Result NMT_tx1
open NNG_Carriers094

def error : verifier.Error → LIB_VCarriers.VErr
 | .Parse=>.Parse | .Semantic=>.Semantic | .Transcript=>.Transcript | .Relation=>.Relation
 | .Merkle=>.Merkle | .Query=>.Query | .Checkpoint=>.Checkpoint | .Allocation=>.Allocation

def port (r : core.result.Result verifier.Prepared verifier.Error × Array aspis_core.field.wide_exact.WideExact 29#usize) :
 LIBC_PreparedLaw.Output :=
 ((match r.1 with | .Ok p=>.ok (toT12 p) | .Err e=>.error (error e)),arr toT3 r.2)

theorem output (r : NMP_Emitted.PreparedOut) : port (NNG_PrepareAdapter094.output r)=NNG_PreparedCall087.port r := by
 rcases r with ⟨reply,g⟩
 cases reply with
 | Err e=>
  cases e <;>
   simp only [port,NNG_PrepareAdapter094.output,NNG_PrepareAdapter094.error,error,NNG_PreparedCall087.port,NNG_PrepareErrors087.error]
  all_goals rw [NNG_Carriers094.arr_inverse fromT3 toT3 fromT3_inverse]
 | Ok p=>
  simp only [port,NNG_PrepareAdapter094.output,NNG_PreparedCall087.port,fromT12_inverse]
  rw [NNG_Carriers094.arr_inverse fromT3 toT3 fromT3_inverse]
#print axioms output

def digest (env : RSL.Env) : aspis_core.digest.Digest32 Unit:=
 ⟨(NNG_PublicSource137.digest env).coremarkerCopyInst,(NNG_PublicSource137.digest env).digest⟩

theorem input (a : NNG_PrepareInput087.Args) (env : RSL.Env) :
 NNG_PrepareAdapter094.input (digest env) (fromT9 a.public_) (NNG_Data137.bytes a.proof) () none (arr fromT3 a.g)=
 NNG_PrepareInput087.input a none env := by
 unfold NNG_PrepareAdapter094.input
 rw [fromT9_inverse,NNG_Carriers094.arr_inverse fromT3 toT3 fromT3_inverse]
 rfl
#print axioms input

theorem call (a : NNG_PrepareInput087.Args) (env : RSL.Env) :
 NNG_PrepareAdapter094.call env (digest env) (fromT9 a.public_) (NNG_Data137.bytes a.proof) () none (arr fromT3 a.g)=
 NMP_ResultTransport.outer NNG_PrepareAdapter094.output
  (NMP_Emitted.prepare (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a none env)) := by
 unfold NNG_PrepareAdapter094.call
 rw [input]
#print axioms call
end AspisR1.NNG_PrepareTransport094
