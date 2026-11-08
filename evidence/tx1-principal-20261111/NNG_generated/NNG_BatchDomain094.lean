import NNG_BatchRoots094
import NNG_PublicSource137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_BatchDomain094
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
/-- The original batch0 domain, with every length, query and root-value
clause derived at the SAME actual source inputs. -/
theorem reached (proof : Slice U8) (p : LIB_VCarriers.Prepared) (folded root0 root1 : Array U8 32#usize)
 (width : proof.val.length=57607)
 (queries : ∀ q∈p.queries.val,q.val<262144)
 (roots : p.roots=Array.make 2#usize [root0,root1])
 (first : root0.val=(proof.val.drop 16).take 32)
 (third : folded.val=(proof.val.drop 7751).take 32) :
 LIBC_BatchMerkle.Domain (LIB_Carriers.bytes proof,p,LIB_Carriers.b32 folded,0) := by
 refine ⟨rfl,?_,?_,NNG_BatchRoots094.parsed proof root1,?_,?_⟩
 · change (proof.val.map _).length=57607
   rw [List.length_map,width]
 · intro j bound
   change (p.queries.val[j]!).val<262144
   have live : j<p.queries.val.length := by rw [p.queries.property];exact bound
   rw [getElem!_pos p.queries.val j live]
   exact queries _ (List.getElem_mem live)
 · rw [LIBC_Bytes.from_native]
   rfl
 · intro k
   change Port3_NativeBatchCalls.rootAt
    (NLL_BatchSource.roots (NFW_PreparedPort.prepared p) (LIB_Env.nativeKey (LIB_Carriers.b32 folded))) k=
    encodeState (OraclePortBatchDraft.committedRoot (NNG_BatchRoots094.parsed proof root1) k.val)
   rw [NNG_PublicSource137.key_native,NNG_BatchRoots094.source_roots _ root0 root1 folded roots]
   exact NNG_BatchRoots094.values proof root0 root1 folded first third k
#print axioms reached
end AspisR1.NNG_BatchDomain094
