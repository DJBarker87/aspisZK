import LIBC_BatchWire
import LIBC_CohortHash
import LIBC_Bytes
import LIBC_ResultGraph
import LIBC_Usize
import LIBC_VStateCarriers
import NLN_TX1_081
set_option autoImplicit false
noncomputable section
namespace LIBC_BatchMerkle
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1
abbrev Args := RSL.Bytes × LIB_VCarriers.Prepared × RSL.B32 × Nat
abbrev Output := Except LIB_VCarriers.VErr Unit
def prepared (a : Args) := NFW_PreparedPort.prepared a.2.1
def folded (a : Args) := LIB_Env.nativeKey a.2.2.1
def parsed (a : Args) : OraclePortCompactDraft.Parsed :=
 ⟨MultiproofConeCanonical.bytesOf (LIBC_Bytes.raw a.1).val,[]⟩
/-- Literal NLO-bf64--67, with the source's batch0 argument. The parsed
witness is own-input provenance, never a native Cut or successful child. -/
def Domain (a : Args) : Prop :=
 a.2.2.2=0 ∧ a.1.length=57607 ∧
 (∀ j,j<22 → (prepared a).queries.val[j]!.val<262144) ∧
 ∃ p : OraclePortCompactDraft.Parsed,
 p.wire=MultiproofConeCanonical.bytesOf (LIBC_Bytes.raw a.1).val ∧
 ∀ k : Fin 3,Port3_NativeBatchCalls.rootAt (NLL_BatchSource.roots (prepared a) (folded a)) k=
 AspisV8R19.SqueezeOracleBridge.encodeState (OraclePortBatchDraft.committedRoot p k.val)
def model (a : Args) (env : RSL.Env) :=
 NLL_Parent.model (LIBC_CohortHash.H env) (LIBC_Bytes.raw a.1) (prepared a).queries
 (LIBC_Usize.raw a.2.2.2) (NLL_Parent.sites (NLL_BatchSource.roots (prepared a) (folded a)))
 NKV_ParentSource.zeroI NKV_ParentSource.zeroV
def history (a : Args) (env : RSL.Env) :=
 NLL_Parent.plan (LIBC_CohortHash.H env) (LIBC_Bytes.raw a.1) (parsed a) (prepared a).queries
 (LIBC_Usize.raw a.2.2.2) (NLL_Parent.sites (NLL_BatchSource.roots (prepared a) (folded a)))
 NKV_ParentSource.zeroI NKV_ParentSource.zeroV
def render (h : NLL.History) : List RSL.Event :=
 h.map (fun e => .digest (LIBC_HashPartitions.split (LIBC_CohortHash.host e.1))
 (LIB_Carriers.b32 (AspisV8R19.SqueezeOracleBridge.encodeState e.2)))
def port : NLL.Reply → Output
 | .Ok _ => .ok () | .Err e => .error (Port3_CheckpointInstall.error e)
def child : RSL.Child Args Output := ⟨Domain,fun a => LIB_Carriers.resultGraph port (model a) (fun env => render (history a env))⟩
def value (a : Args) (env : RSL.Env) : Output := LIBC_ResultGraph.value port (.error .Merkle) (model a env)
theorem returns (a : Args) (env : RSL.Env) : NND_Returned.Returns (child.law a) env (value a env) :=
 LIBC_ResultGraph.returns _ _ _ _ env
theorem source (a : Args) (env : RSL.Env) :
 model a env = NKV_FRef.verifier.candidate.batch_merkle (NKV_ConcreteChildren.ops (LIBC_CohortHash.H env))
 (NKV_ConcreteChildren.digest (LIBC_CohortHash.H env)) (LIBC_Bytes.raw a.1) (prepared a) (folded a)
 (LIBC_Usize.raw a.2.2.2) () := by
 rw [NLL_BatchSource.source,NLL_ParentSource.source]
 rfl
theorem root (a : Args) (env : RSL.Env) (domain : Domain a)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=(parsed a).wire)
 (roots : ∀ k : Fin 3,Port3_NativeBatchCalls.rootAt (NLL_BatchSource.roots (prepared a) (folded a)) k=
 AspisV8R19.SqueezeOracleBridge.encodeState (OraclePortBatchDraft.committedRoot p k.val)) :
 NLN.BatchPacket (LIBC_CohortHash.H env) (LIBC_Bytes.raw a.1) p (prepared a) (folded a) 0#usize := by
 have bound : a.1.length ≤ Usize.max := by rw [domain.2.1];scalar_tac
 apply NLN_TX1_081.root _ _ _ p wire _ _ domain.2.2.1 roots
 rw [LIBC_Bytes.raw_length _ bound,domain.2.1]
/-- Returned Err is a returned Merkle error, never collapsed to a panic.
The root's full source-ordered history is reified without choosing a native
relation to define the law. -/
theorem returning (a : Args) (env : RSL.Env) (domain : Domain a)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=(parsed a).wire)
 (roots : ∀ k : Fin 3,Port3_NativeBatchCalls.rootAt (NLL_BatchSource.roots (prepared a) (folded a)) k=
 AspisV8R19.SqueezeOracleBridge.encodeState (OraclePortBatchDraft.committedRoot p k.val))
 (h : NLL.History) (out : NLL.Reply)
 (native : NLL_BatchSource.Invocation (LIBC_CohortHash.H env) (LIBC_Bytes.raw a.1) (prepared a) (folded a) 0#usize h out) :
 child.law a env ⟨.ret (port out),render h⟩ := by
 have packet := (root a env domain p wire roots).returning h out native
 have zero : LIBC_Usize.raw a.2.2.2=0#usize := by rw [domain.1];exact LIBC_Usize.from_native 0#usize (by scalar_tac)
 have same : history a env=h := by
  unfold history
  rw [zero,← LIBC_BatchWire.plan _ _ p (parsed a) wire]
  exact packet.2.1
 change _ = LIB_Carriers.resultObs port (render (history a env)) (model a env)
 rw [same,source,zero,packet.1]
 rfl
#print axioms returns
#print axioms source
#print axioms root
#print axioms returning
end LIBC_BatchMerkle
