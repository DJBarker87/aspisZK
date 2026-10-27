import R1Z.PV_OptB_Cardinality
import R1Z.PV_OptB_AdmittedFamily
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_FieldCard
open R0P AspisR1.SpendRelation
abbrev M := R1J.SpendWitnessMap.F

theorem cardM : Fintype.card M = 2147483647 := by
  change Fintype.card (ZMod 2147483647) = 2147483647
  exact ZMod.card 2147483647

theorem cardDigest_generic (A : Type) [Fintype A] :
    Fintype.card (Digest A) = Fintype.card A ^ 8 := by simp [Digest]

theorem cardDigest : Fintype.card (Digest M) = 2147483647^8 :=
  (cardDigest_generic M).trans (congrArg (fun n : Nat => n^8) cardM)

theorem large : Fintype.card (Digest M) * 4096^16 < Fintype.card M ^ 16 := by
  rw [cardDigest,cardM]
  exact PV_OptB_Cardinality.sparse_cardinality

theorem large_for {A : Type} [Fintype A] (card : Fintype.card A = 2147483647) :
    Fintype.card (Digest A) * 4096^16 < Fintype.card A ^ 16 := by
  rw [cardDigest_generic,card]
  exact PV_OptB_Cardinality.sparse_cardinality

#print axioms cardM
#print axioms cardDigest_generic
#print axioms cardDigest
#print axioms large
#print axioms large_for
end R1Z.PV_OptB_FieldCard
