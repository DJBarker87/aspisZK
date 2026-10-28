import PV_2TNV_Node01
import PV_2TNV_Node02
import PV_2TNV_Node03
import PV_2TNV_Node04
import PV_2TNV_Node05
import PV_2TNV_Node06
import PV_2TNV_Node07
import PV_2TNV_Node08
import PV_2TNV_Node09
import PV_2TNV_Node10
import PV_2TNV_Node11
import PV_2TNV_Node12
import PV_2TNV_Node13
import PV_2TNV_Node14
import PV_2TNV_Node15
import PV_2TNV_Node16
import PV_2TNV_Node17
import PV_2TNV_Node18
import PV_2TNV_Node19
import PV_2TNV_Node20
import PV_2TNV_PublicLiterals
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_AppendBinding
open R0P AspisR1 PV_2TNV_PublicEncoding PV_2TNV_PublicLiterals
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation
theorem prefix01 : AppendPath.pathPrefix nativePublic pair 1 = PV_2TNV_Node01.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  unfold AppendPath.step
  rw [if_neg (show ¬digestBitZero nativePublic ⟨0,by decide⟩ by
    change ¬((nativePublic.nextPairIndex >>> 0) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [frontier00]
  change nodeCompress PV_2TNV_Node01.left PV_2TNV_Node01.right = PV_2TNV_Node01.output
  exact PV_2TNV_Node01.source
#print axioms prefix01
theorem prefix02 : AppendPath.pathPrefix nativePublic pair 2 = PV_2TNV_Node02.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix01]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨1,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 1) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node02.left PV_2TNV_Node02.right = PV_2TNV_Node02.output
  exact PV_2TNV_Node02.source
#print axioms prefix02
theorem prefix03 : AppendPath.pathPrefix nativePublic pair 3 = PV_2TNV_Node03.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix02]
  unfold AppendPath.step
  rw [if_neg (show ¬digestBitZero nativePublic ⟨2,by decide⟩ by
    change ¬((nativePublic.nextPairIndex >>> 2) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [frontier02]
  change nodeCompress PV_2TNV_Node03.left PV_2TNV_Node03.right = PV_2TNV_Node03.output
  exact PV_2TNV_Node03.source
#print axioms prefix03
theorem prefix04 : AppendPath.pathPrefix nativePublic pair 4 = PV_2TNV_Node04.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix03]
  unfold AppendPath.step
  rw [if_neg (show ¬digestBitZero nativePublic ⟨3,by decide⟩ by
    change ¬((nativePublic.nextPairIndex >>> 3) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [frontier03]
  change nodeCompress PV_2TNV_Node04.left PV_2TNV_Node04.right = PV_2TNV_Node04.output
  exact PV_2TNV_Node04.source
#print axioms prefix04
theorem prefix05 : AppendPath.pathPrefix nativePublic pair 5 = PV_2TNV_Node05.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix04]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨4,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 4) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node05.left PV_2TNV_Node05.right = PV_2TNV_Node05.output
  exact PV_2TNV_Node05.source
#print axioms prefix05
theorem prefix06 : AppendPath.pathPrefix nativePublic pair 6 = PV_2TNV_Node06.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix05]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨5,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 5) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node06.left PV_2TNV_Node06.right = PV_2TNV_Node06.output
  exact PV_2TNV_Node06.source
#print axioms prefix06
theorem prefix07 : AppendPath.pathPrefix nativePublic pair 7 = PV_2TNV_Node07.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix06]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨6,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 6) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node07.left PV_2TNV_Node07.right = PV_2TNV_Node07.output
  exact PV_2TNV_Node07.source
#print axioms prefix07
theorem prefix08 : AppendPath.pathPrefix nativePublic pair 8 = PV_2TNV_Node08.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix07]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨7,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 7) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node08.left PV_2TNV_Node08.right = PV_2TNV_Node08.output
  exact PV_2TNV_Node08.source
#print axioms prefix08
theorem prefix09 : AppendPath.pathPrefix nativePublic pair 9 = PV_2TNV_Node09.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix08]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨8,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 8) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node09.left PV_2TNV_Node09.right = PV_2TNV_Node09.output
  exact PV_2TNV_Node09.source
#print axioms prefix09
theorem prefix10 : AppendPath.pathPrefix nativePublic pair 10 = PV_2TNV_Node10.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix09]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨9,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 9) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node10.left PV_2TNV_Node10.right = PV_2TNV_Node10.output
  exact PV_2TNV_Node10.source
#print axioms prefix10
theorem prefix11 : AppendPath.pathPrefix nativePublic pair 11 = PV_2TNV_Node11.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix10]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨10,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 10) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node11.left PV_2TNV_Node11.right = PV_2TNV_Node11.output
  exact PV_2TNV_Node11.source
#print axioms prefix11
theorem prefix12 : AppendPath.pathPrefix nativePublic pair 12 = PV_2TNV_Node12.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix11]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨11,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 11) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node12.left PV_2TNV_Node12.right = PV_2TNV_Node12.output
  exact PV_2TNV_Node12.source
#print axioms prefix12
theorem prefix13 : AppendPath.pathPrefix nativePublic pair 13 = PV_2TNV_Node13.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix12]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨12,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 12) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node13.left PV_2TNV_Node13.right = PV_2TNV_Node13.output
  exact PV_2TNV_Node13.source
#print axioms prefix13
theorem prefix14 : AppendPath.pathPrefix nativePublic pair 14 = PV_2TNV_Node14.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix13]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨13,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 13) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node14.left PV_2TNV_Node14.right = PV_2TNV_Node14.output
  exact PV_2TNV_Node14.source
#print axioms prefix14
theorem prefix15 : AppendPath.pathPrefix nativePublic pair 15 = PV_2TNV_Node15.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix14]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨14,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 14) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node15.left PV_2TNV_Node15.right = PV_2TNV_Node15.output
  exact PV_2TNV_Node15.source
#print axioms prefix15
theorem prefix16 : AppendPath.pathPrefix nativePublic pair 16 = PV_2TNV_Node16.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix15]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨15,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 15) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node16.left PV_2TNV_Node16.right = PV_2TNV_Node16.output
  exact PV_2TNV_Node16.source
#print axioms prefix16
theorem prefix17 : AppendPath.pathPrefix nativePublic pair 17 = PV_2TNV_Node17.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix16]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨16,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 16) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node17.left PV_2TNV_Node17.right = PV_2TNV_Node17.output
  exact PV_2TNV_Node17.source
#print axioms prefix17
theorem prefix18 : AppendPath.pathPrefix nativePublic pair 18 = PV_2TNV_Node18.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix17]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨17,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 17) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node18.left PV_2TNV_Node18.right = PV_2TNV_Node18.output
  exact PV_2TNV_Node18.source
#print axioms prefix18
theorem prefix19 : AppendPath.pathPrefix nativePublic pair 19 = PV_2TNV_Node19.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix18]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨18,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 18) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node19.left PV_2TNV_Node19.right = PV_2TNV_Node19.output
  exact PV_2TNV_Node19.source
#print axioms prefix19
theorem prefix20 : AppendPath.pathPrefix nativePublic pair 20 = PV_2TNV_Node20.output := by
  rw [AppendPath.pathPrefix, dif_pos (by decide)]
  rw [prefix19]
  unfold AppendPath.step
  rw [if_pos (show digestBitZero nativePublic ⟨19,by decide⟩ by
    change ((nativePublic.nextPairIndex >>> 19) &&& 1) = 0
    rw [native_index]
    decide)]
  rw [R1Z.PV_RunJoin_RootModel.frozen_literal]
  change nodeCompress PV_2TNV_Node20.left PV_2TNV_Node20.right = PV_2TNV_Node20.output
  exact PV_2TNV_Node20.source
#print axioms prefix20
theorem source : SpendRelation.AppendBinding nativePublic := by
  refine ⟨pair,output_pair,?_,?_⟩
  · rw [nextRoot,prefix20]
    rfl
  · intro hc
    have index : digestCarry nativePublic.nextPairIndex = 1 := by
      rw [native_index]
      decide
    simp only [index]
    rw [carry,prefix01]
    rfl
#print axioms source
end AspisR1.PV_2TNV_AppendBinding
