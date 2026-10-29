import NDI_BatchRef.Funs
set_option autoImplicit false
namespace NDI_BatchWord
open Aeneas Aeneas.Std Result

theorem word (u : U32) (tree coordinate : Usize) (bound : coordinate.val<16) :
    ∃ out, NDI_BatchRef.batch_word_ref u tree coordinate=ok out ∧
      out.val=256*(if tree=2#usize then u.val/4 else u.val)+coordinate.val := by
  obtain ⟨index,div,indexVal⟩ := UScalar.div_spec (x:=u) (y:=4#u32) (by decide)
  have convert (x : U32) : (UScalar.cast .U64 x).val=x.val := UScalar.cast_val_eq
  by_cases tag : tree=2#usize
  · have b := index.hmax
    obtain ⟨product,mul,pval⟩ := WP.spec_imp_exists
      (U64.mul_spec (x:=UScalar.cast .U64 index) (y:=256#u64) (by scalar_tac))
    obtain ⟨out,add,oval⟩ := WP.spec_imp_exists
      (U64.add_spec (x:=product) (y:=UScalar.cast .U64 coordinate) (by scalar_tac))
    refine ⟨out,?_,?_⟩
    · simp only [NDI_BatchRef.batch_word_ref,if_pos tag,div,bind_tc_ok,
        core.convert.num.FromU64U32.from,lift,convert,mul,add]
    · simp only [tag,if_true] ; scalar_tac
  · have b := u.hmax
    obtain ⟨product,mul,pval⟩ := WP.spec_imp_exists
      (U64.mul_spec (x:=UScalar.cast .U64 u) (y:=256#u64) (by scalar_tac))
    obtain ⟨out,add,oval⟩ := WP.spec_imp_exists
      (U64.add_spec (x:=product) (y:=UScalar.cast .U64 coordinate) (by scalar_tac))
    refine ⟨out,?_,?_⟩
    · simp only [NDI_BatchRef.batch_word_ref,if_neg tag,bind_tc_ok,
        core.convert.num.FromU64U32.from,lift,mul,add]
    · simp only [tag,if_false] ; scalar_tac

#print axioms word
end NDI_BatchWord
