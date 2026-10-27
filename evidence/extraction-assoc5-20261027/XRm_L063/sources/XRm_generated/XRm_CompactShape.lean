import XRk_Funs
import XRk_ResultTools
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools
namespace XRm_CompactShape
/-- Accepted emitted compact parsing uses the SAME physical proof, magic
comparison, tag and reserved-byte scan; no second parse witness is supplied. -/
theorem accepted (proof : Slice U8) (variant : transport.Variant)
    (run : verifier.candidate.parse_shape proof=ok (.Ok variant)) :
    variant=.S2 ∧ ∃ size magic tag reserved it last,
      compact.PROOF_BYTES=ok size ∧ Slice.len proof=size ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        proof ⟨8#usize⟩=ok magic ∧
      core.cmp.impls.PartialEqShared.ne (Slice.Insts.CoreCmpPartialEqArray 8#usize core.cmp.PartialEqU8)
        magic compact.MAGIC=ok false ∧
      Slice.index_usize proof 8#usize=ok tag ∧ transport.Variant.tag .S2=ok tag ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof ⟨9#usize,16#usize⟩=ok reserved ∧ core.slice.Slice.iter reserved=ok it ∧
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
        verifier.candidate.parse_shape.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool
        it ()=ok (false,last) := by
  unfold verifier.candidate.parse_shape at run
  obtain ⟨size,hsize,run⟩ := bind_success _ _ _ run
  split at run
  · cases run
  · rename_i hlength
    have length : Slice.len proof=size := by simpa only [bne_iff_ne,not_not] using hlength
    obtain ⟨magic,hmagic,run⟩ := bind_success _ _ _ run
    obtain ⟨different,hdifferent,run⟩ := bind_success _ _ _ run
    cases different with
    | true => cases run
    | false =>
      obtain ⟨tag,htag,run⟩ := bind_success _ _ _ run
      obtain ⟨expected,hexpected,run⟩ := bind_success _ _ _ run
      split at run
      · cases run
      · rename_i htagged
        have same : tag=expected := by simpa only [bne_iff_ne,not_not] using htagged
        subst expected
        obtain ⟨reserved,hreserved,run⟩ := bind_success _ _ _ run
        obtain ⟨it,hit,run⟩ := bind_success _ _ _ run
        obtain ⟨bad,last,hany,run⟩ := pair_bind_success _ _ _ run
        cases bad with
        | true => cases run
        | false =>
          have hv := core.result.Result.Ok.inj (Result.ok.inj run)
          exact ⟨hv.symm,size,magic,tag,reserved,it,last,hsize,length,hmagic,hdifferent,htag,hexpected,hreserved,hit,hany⟩
#print axioms accepted
end XRm_CompactShape
