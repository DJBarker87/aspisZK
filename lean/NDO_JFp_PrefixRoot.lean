import NDO_JFp_InitBytes
import NDO_JFw_RealExpansion
set_option autoImplicit false
namespace AspisR1.JFp_PrefixRoot
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation
open JFx_NativeBytes

theorem retained : (proof.val.drop 16).take 32=JFp_InitBytes.root.val := by
  change (proofBytes.drop 16).take 32 = _
  simp only [proofBytes,List.drop_append,List.take_append,List.length_append,
    JFx_DataProof00.length,
    JFx_DataProof01.length,
    JFx_DataProof02.length,
    JFx_DataProof03.length,
    JFx_DataProof04.length,
    JFx_DataProof05.length,
    JFx_DataProof06.length,
    JFx_DataProof07.length,
    JFx_DataProof08.length,
    JFx_DataProof09.length,
    JFx_DataProof10.length,
    JFx_DataProof11.length,
    JFx_DataProof12.length,
    JFx_DataProof13.length,
    JFx_DataProof14.length,
    Nat.reduceAdd,Nat.reduceSub,List.take_zero,List.append_nil,List.drop_zero,List.nil_append,List.drop_eq_nil_of_le,List.length_drop,Nat.reduceLeDiff,List.take_of_length_le]
  simp only [JFx_DataProof00.bytes,List.drop_append,List.take_append,List.length_append,
    JFx_DataProof00.c00_length,JFx_DataProof00.c01_length,
    JFx_DataProof00.c02_length,JFx_DataProof00.c03_length,
    JFx_DataProof00.c04_length,JFx_DataProof00.c05_length,
    JFx_DataProof00.c06_length,JFx_DataProof00.c07_length,
    JFx_DataProof00.c08_length,JFx_DataProof00.c09_length,
    JFx_DataProof00.c10_length,JFx_DataProof00.c11_length,
    JFx_DataProof00.c12_length,JFx_DataProof00.c13_length,
    JFx_DataProof00.c14_length,JFx_DataProof00.c15_length,
    JFx_DataProof00.c16_length,JFx_DataProof00.c17_length,
    JFx_DataProof00.c18_length,JFx_DataProof00.c19_length,
    JFx_DataProof00.c20_length,JFx_DataProof00.c21_length,
    JFx_DataProof00.c22_length,JFx_DataProof00.c23_length,
    JFx_DataProof00.c24_length,JFx_DataProof00.c25_length,
    JFx_DataProof00.c26_length,JFx_DataProof00.c27_length,
    JFx_DataProof00.c28_length,JFx_DataProof00.c29_length,
    JFx_DataProof00.c30_length,JFx_DataProof00.c31_length,
    JFx_DataProof00.c32_length,JFx_DataProof00.c33_length,
    JFx_DataProof00.c34_length,JFx_DataProof00.c35_length,
    JFx_DataProof00.c36_length,JFx_DataProof00.c37_length,
    JFx_DataProof00.c38_length,JFx_DataProof00.c39_length,
    JFx_DataProof00.c40_length,JFx_DataProof00.c41_length,
    JFx_DataProof00.c42_length,JFx_DataProof00.c43_length,
    JFx_DataProof00.c44_length,JFx_DataProof00.c45_length,
    JFx_DataProof00.c46_length,JFx_DataProof00.c47_length,
    JFx_DataProof00.c48_length,JFx_DataProof00.c49_length,
    JFx_DataProof00.c50_length,JFx_DataProof00.c51_length,
    JFx_DataProof00.c52_length,JFx_DataProof00.c53_length,
    JFx_DataProof00.c54_length,JFx_DataProof00.c55_length,
    JFx_DataProof00.c56_length,JFx_DataProof00.c57_length,
    JFx_DataProof00.c58_length,JFx_DataProof00.c59_length,
    JFx_DataProof00.c60_length,JFx_DataProof00.c61_length,
    JFx_DataProof00.c62_length,JFx_DataProof00.c63_length,
    Nat.reduceAdd,Nat.reduceSub,List.take_zero,List.append_nil,List.drop_zero,List.nil_append,List.drop_eq_nil_of_le,List.length_drop,Nat.reduceLeDiff,List.take_of_length_le]
  rfl


theorem source (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored
      JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) : pre.c1_root=JFp_InitBytes.root := by
  apply Subtype.ext
  rw [PSem_Root.source_root _ _ _ _ expand parse]
  change (((proof.val.drop 16).take 7015).take 32)=JFp_InitBytes.root.val
  rw [List.take_take]
  exact retained

#print axioms retained
#print axioms source
end AspisR1.JFp_PrefixRoot
