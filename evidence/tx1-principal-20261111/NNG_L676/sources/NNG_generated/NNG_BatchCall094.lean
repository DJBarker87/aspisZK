import NNG_StateCalls094
import LIBC_BatchGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_BatchCall094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Carriers094 NNG_StateCalls094

def fromExcept {A B : Type} (f : A → B) : Except LIB_VCarriers.VErr A → core.result.Result B verifier.Error
 | .ok a=>.Ok (f a) | .error e=>.Err (NNG_ParseCall094.errorBack e)
theorem inverse {A : Type} (r : Except LIB_VCarriers.VErr A) : port id (fromExcept id r)=r := by
 cases r with
 | ok a=>rfl
 | error e=>exact congrArg Except.error (NNG_ParseCall094.error_inverse e)
#print axioms inverse

def args (proof : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize) (batch : Usize) : LIBC_BatchMerkle.Args :=
 (LIB_Carriers.bytes proof,toT12 p,LIB_Carriers.b32 root,batch.val)
def call (env : RSL.Env) (proof : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize) (batch : Usize) :=
 NMP_ResultTransport.outer (fromExcept id ∘ LIBC_BatchMerkle.port) (LIBC_BatchMerkle.model (args proof p root batch) env)
def events (env : RSL.Env) (proof : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize) (batch : Usize) :=
 LIBC_BatchMerkle.render (LIBC_BatchMerkle.history (args proof p root batch) env)

theorem graph (env : RSL.Env) (proof : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize) (batch : Usize)
 (domain : LIBC_BatchMerkle.Domain (args proof p root batch)) :
 LIBC_BatchMerkle.child.run (args proof p root batch) env
  (LIB_Carriers.resultObs (port id) (events env proof p root batch) (call env proof p root batch)) := by
 refine ⟨domain,?_⟩
 apply (LIBC_BatchMerkle.graph _ env _).mpr
 apply obs_outer
 intro r
 exact inverse _
#print axioms graph

theorem source (env : RSL.Env) (proof : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize) (batch : Usize) :
 call env proof p root batch=NMP_ResultTransport.outer (fromExcept id ∘ LIBC_BatchMerkle.port)
  (AspisR1.NKV_FRef.verifier.candidate.batch_merkle
   (AspisR1.NKV_ConcreteChildren.ops (LIBC_CohortHash.H env))
   (AspisR1.NKV_ConcreteChildren.digest (LIBC_CohortHash.H env))
   (LIBC_Bytes.raw (args proof p root batch).1) (LIBC_BatchMerkle.prepared (args proof p root batch))
   (LIBC_BatchMerkle.folded (args proof p root batch)) (LIBC_Usize.raw batch.val) ()) := by
 unfold call
 rw [LIBC_BatchMerkle.source]
#print axioms source
end AspisR1.NNG_BatchCall094
