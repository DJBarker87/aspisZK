import NIF_FieldsTotal
import NIF_QueryEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIF_EntryFields
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NHL_Tx1Stages
open OraclePortCompactDraft MultiproofConeCanonical
/-- The SAME query index and proof supplied by the TX1 prefix construct the
entire fields reply. This exports a caller-domain fact, never an extra child
success premise. The generic arbitrary-byte NFS root is unchanged. -/
theorem entered (base : Ops) {H : Type} (prepareCall : NHL_EmittedTx1.Prepare H)
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (public_bytes proof : Slice U8) (k : Usize) (hash : H) (context : Context)
 (length : proof.val.length=57607)
 (reached : beforeQuery (Op4P_Install.install base) prepareCall D pub public_bytes proof k hash none=ok (.Ok context))
 (seed : Port3_NativeQueryBody.Ops) (i : Usize) (inside : i.val<22) :
 ∃ q, Port4B_Opening.opening proof i=ok q ∧ q.val.length=832 ∧
 canonical (slice (bytesOf q.val) 672 128) ∧
 ∃ values, (NFS_CallerDomains.ops seed).op0 4#usize
 (Port3_NativeQueryBody.verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
  (NFS_CallerDomains.ops seed)) q=ok values := by
 obtain ⟨q,hq,size,same⟩:=Port4B_Opening.opening_exact proof length i inside
 have hcanonical := NIF_ScanDomain.reached_fields base prepareCall D pub public_bytes proof k hash context length reached i.val inside
 have cq : canonical (slice (bytesOf q.val) 672 128) := by rw [same];exact hcanonical
 exact ⟨q,hq,size,cq,NIF_FieldsTotal.fields seed q size cq⟩
#print axioms entered
end AspisR1.NIF_EntryFields
