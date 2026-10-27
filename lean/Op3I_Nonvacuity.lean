import Op3I_Cuts
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Op3I_Nonvacuity
open AspisR1CurrentCaller Op3I_Install

/-- The specialized existing D188 premise is inhabited for every remaining
operation dictionary, semantic boundary and std Claims implementation. This is
consistency of the association, not certification of native deployment. -/
theorem extraction_satisfiable (adapterOps : AdapterRw.Ops) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) :
    ∃ native1 native2,
      S2W_DigestExtraction.AeneasExtraction
        (ClaimsUnrolledSdk.sdkOps
          {adapterOps with op43 := S2W_DigestExtraction.digest hashv} (install ops) B std)
        native1 native2 hashv := by
  let actual := ClaimsUnrolledSdk.sdkOps
    {adapterOps with op43 := S2W_DigestExtraction.digest hashv} (install ops) B std
  exact ⟨AdapterRw.r1_pool_adapter.owned.stage1_owned actual,
    AdapterRw.r1_pool_adapter.owned.stage2_owned actual,⟨by intros; rfl,by intros; rfl,by intros; rfl⟩⟩

theorem source_of_fields (proof : Slice U8)
    (length : proof.val.length = 57607)
    (magic : proof.val.take 8 = Op3I_Source.compact.MAGIC.val)
    (tag : proof.val[8]? = some 2#u8)
    (tail : (proof.val.drop 9).take 7 = List.replicate 7 0#u8) :
    sourceBody proof = ok (.Ok .S2) := by
  have len : Slice.len proof = 57607#usize := by
    apply UScalar.eq_of_val_eq
    simpa using length
  have bound8 : 8#usize ≤ proof.length := by scalar_tac
  have bound16 : 9#usize ≤ 16#usize ∧ 16#usize ≤ proof.length := by scalar_tac
  have tagValue : proof.val[8]'(by omega) = 2#u8 := by
    exact Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans tag)
  have nozero := Op3I_Header.any_exact (List.replicate 7 0#u8)
  obtain ⟨n,hn⟩ := nozero
  have body : Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops proof = ok (.Ok .S2) := by
    simp only [Op3I_Source.verifier.candidate.parse_shape,Op3I_Header.proof_bytes,
      bind_tc_ok,len,bne_self_eq_false,Bool.false_eq_true,if_false,
      core.slice.index.Slice.index,core.slice.index.SliceIndexRangeToUsizeSlice.index,
      bound8,if_true,core.cmp.impls.PartialEqShared.ne,Op3I_Std.ops,
      Op3I_Std.eqList_u8,List.slice,
      show (8#usize).val = 8 by scalar_tac, show (9#usize).val = 9 by scalar_tac,
      show (16#usize).val = 16 by scalar_tac, Nat.sub_zero,
      show 16-9 = 7 by decide, List.drop_zero,magic,decide_true,
      Bool.not_true,Slice.index_usize,tag,Op3I_Source.transport.Variant.tag,
      core.slice.index.SliceIndexRangeUsizeSlice.index,bound16,
      core.slice.Slice.iter,tail,hn,List.any_replicate]
    simp [Slice.length,length,tagValue,Op3I_Std.anyList,
      Op3I_Source.verifier.candidate.parse_shape.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool,
      Op3I_Source.verifier.candidate.parse_shape.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool.call_mut]
  simp only [sourceBody,body,bind_tc_ok,currentVariant]

#print axioms extraction_satisfiable
#print axioms source_of_fields
end AspisR1.Op3I_Nonvacuity
end
