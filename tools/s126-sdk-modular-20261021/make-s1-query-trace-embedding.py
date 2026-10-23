from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';P=B/'lean/bridge-opening-queries-1b98-20261017/ExtractedOpeningQueriesModel.lean';raw=P.read_text();a=raw.index('def QueriesModel.queries (');b=raw.index('\ndef QueriesModel.entry',a);fun=raw[a:b]
start=fun.index('    let u ← Array.index_usize q 0#usize');end=fun.index('\n  | core.ops.control_flow.ControlFlow.Break residual',start);tail=fun[start:end];assert tail.count('B.embed')==22
head='''import S1M31EmbeddingTotalV1
import CurrentOriginalPreparedInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1PublicPreparation.S1QueryTraceEmbedding
abbrev actualEmbed := AspisS1M31Embedding.Total.embed

theorem embedTrace_total {A : Type} (u : U32) (i : Usize) (tail : Result A) :
    (do let w ← actualEmbed u;trace.value 5#u16 i w;tail)=tail := by
  simp only [actualEmbed,AspisS1M31Embedding.Total.embed_total,bind_tc_ok,trace.value]

theorem indexUnused_total {A : Type} (q : Array U32 22#usize) (i : Usize)
    (hi : i.val<22) (tail : Result A) : (do let _ ← Array.index_usize q i;tail)=tail := by
  have bound : i.val<q.val.length := by rw [q.property];exact hi
  obtain ⟨u,read,_⟩ := WP.spec_imp_exists (Array.index_usize_spec q i bound)
  rw [read,bind_tc_ok]

'''
taildef='''def tracedTail {H : Type} (q : Array U32 22#usize) (self1 : transcript.Transcript H)
    (state7 : Array U8 32#usize) :
    Result (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H) := do
'''+tail.replace('B.embed','actualEmbed')+'\n'
lem='''
theorem tracedTail_total {H : Type} (q : Array U32 22#usize) (self1 : transcript.Transcript H)
    (state7 : Array U8 32#usize) : tracedTail q self1 state7=
      ok (core.result.Result.Ok q,{self1 with state:=state7}) := by
  unfold tracedTail
  simp (disch := decide) only [embedTrace_total,indexUnused_total]

'''
withtrace=fun.replace('def QueriesModel.queries (','def queriesWithTrace (',1).replace(tail,'    tracedTail q self1 state7')
without=fun.replace('def QueriesModel.queries (','def queriesWithoutTrace (',1).replace(tail,'    ok (core.result.Result.Ok q, { self1 with state := state7 })')
proof='''
private theorem bind_congr {A B : Type} (m : Result A) (f g : A → Result B)
    (same : ∀ a,f a=g a) : (do let a ← m;f a)=(do let a ← m;g a) := by
  cases m with
  | ok a => exact same a
  | fail e => rfl
  | div => rfl

/-- COMPLETE Result identity: actual default-release trace embeddings cannot
introduce failure/divergence or change the selected queries/transcript state.
All original absorb/digest/decode/rejection paths remain, with no successful
caller, digest-totality, scan-totality or embedding-law premise. -/
theorem queries_actual_embed {H : Type} (B : QueriesModel.Boundaries)
    (D : aspis_core.Digest32 H) (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    QueriesModel.queries {B with embed:=actualEmbed} D self row payload=
      queriesWithoutTrace B D self row payload := by
  unfold QueriesModel.queries queriesWithoutTrace
  repeat' (apply bind_congr;intro x)
  split <;> simp (disch := decide) only [embedTrace_total,indexUnused_total]

#print axioms embedTrace_total
#print axioms indexUnused_total
#print axioms tracedTail_total
#print axioms queries_actual_embed
end AspisR1PublicPreparation.S1QueryTraceEmbedding
'''
out=head+taildef+lem+withtrace+'\n'+without+'\n'+proof;(S/'S1QueryTraceEmbeddingV1.lean').write_text(out)
(S/'s1-query-trace-fission.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source=str(P.relative_to(R)),source_sha256=hashlib.sha256(raw.encode()).hexdigest(),tail_sha256=hashlib.sha256(tail.encode()).hexdigest(),source_sha256_out=hashlib.sha256(out.encode()).hexdigest(),trace_count=22,qualification='Exact original query-model prefix and rejection body copied;22-entry tail factored. Kernel factored equality and total trace proof are mandatory. Actual SDK/caller/hash/scan/full-source bindings remain.'),indent=2)+'\n')
