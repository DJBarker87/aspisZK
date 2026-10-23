import S9CheckpointSemanticReadOnlyV1
import S9ReaderKActualQMCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CheckpointSemanticAlphaCanonicalV1
open AspisR1Stage2
open AspisR1S9CheckpointSemanticReadOnlyV1

/-- Generic preservation for the existing sequential-reader model. Success
and every read witness come from the same run, including all early errors. -/
theorem read_list_canonical (read : ReadK) (P : K → Prop)
    (hread : ∀ r r1 q, read r = .ok (.Ok q,r1) → P q)
    (n : Nat) (r last : verifier.Reader) (xs : List K)
    (success : readList read n r = .ok (.Ok (xs,last))) : ∀ q ∈ xs, P q := by
  induction n generalizing r xs with
  | zero =>
    have he := core.result.Result.Ok.inj (Result.ok.inj success)
    have hxs : [] = xs := congrArg Prod.fst he
    rw [← hxs]
    intro q hq
    cases hq
  | succ n ih =>
    unfold readList at success
    obtain ⟨⟨value,out⟩,hfirst,tail⟩ := AspisR1S9CheckpointSemanticReadOnlyV1.bind_success _ _ _ success
    cases value with
    | Err e => cases tail
    | Ok x =>
      obtain ⟨rest,run,tail⟩ := AspisR1S9CheckpointSemanticReadOnlyV1.bind_success _ _ _ tail
      cases rest with
      | Err e => cases tail
      | Ok pair =>
        rcases pair with ⟨ys,finish⟩
        have he := core.result.Result.Ok.inj (Result.ok.inj tail)
        have hxs : x::ys = xs := congrArg Prod.fst he
        have hlast : finish = last := congrArg Prod.snd he
        subst last
        rw [← hxs]
        intro q hq
        rcases List.mem_cons.mp hq with hhead | htail
        · subst q
          exact hread r out x hfirst
        · exact ih out ys run q htail

/-- The existing ten-read helper, instantiated with the concrete strict
checkpoint decoder. Raw reading and helper/caller Rust correspondence remain
explicit source boundaries; no successful decoder/canonical output is assumed. -/
def semanticAlpha (raw : (n : Usize) → verifier.Reader → Result (Array U8 n × verifier.Reader)) :=
  semanticUsing (AspisR1S9ReaderKActualQMCanonicalV1.readerK raw)

theorem semantic_alpha_success_canonical
    (raw : (n : Usize) → verifier.Reader → Result (Array U8 n × verifier.Reader))
    (bytes : Slice U8) (start finish : Usize) (values : Array K 10#usize)
    (success : semanticAlpha raw bytes start = .ok (.Ok (values,finish))) :
    ∀ q ∈ values.val, AspisR1S9ReaderKActualQMCanonicalV1.Canonical q := by
  obtain ⟨last,run,_⟩ := AspisR1S9CheckpointSemanticReadOnlyV1.semantic_fields
    (AspisR1S9ReaderKActualQMCanonicalV1.readerK raw) bytes start finish values success
  exact read_list_canonical (AspisR1S9ReaderKActualQMCanonicalV1.readerK raw)
    AspisR1S9ReaderKActualQMCanonicalV1.Canonical
    (AspisR1S9ReaderKActualQMCanonicalV1.readerK_success_canonical raw)
    10 ⟨bytes,start⟩ last values.val run

theorem semantic_alpha_reads_canonical
    (raw : (n : Usize) → verifier.Reader → Result (Array U8 n × verifier.Reader))
    (bytes : Slice U8) (start finish : Usize) (values : Array K 10#usize)
    (success : semanticAlpha raw bytes start = .ok (.Ok (values,finish)))
    (i : Usize) (q : K) (hindex : Array.index_usize values i = .ok q) :
    AspisR1S9ReaderKActualQMCanonicalV1.Canonical q := by
  cases hget : values[i]? with
  | none =>
    simp only [Array.index_usize,hget] at hindex
    cases hindex
  | some value =>
    simp only [Array.index_usize,hget] at hindex
    have he : value = q := Result.ok.inj hindex
    have hget' : values.val[i.val]? = some value := by simpa using hget
    have hmem : value ∈ values.val := List.mem_of_getElem? hget'
    rw [← he]
    exact semantic_alpha_success_canonical raw bytes start finish values success value hmem

#print axioms read_list_canonical
#print axioms semantic_alpha_success_canonical
#print axioms semantic_alpha_reads_canonical
end AspisR1S9CheckpointSemanticAlphaCanonicalV1
