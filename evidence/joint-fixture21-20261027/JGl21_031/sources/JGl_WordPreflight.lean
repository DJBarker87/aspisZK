import JGl_WordProof
set_option autoImplicit false
namespace AspisR1.JGl_WordPreflight
open JGd_ExactWords
attribute [local irreducible] HAdd.hAdd HSub.hSub HMul.hMul

theorem plus : value ((1,2),(3,4))+value ((4,3),(2,1))=value ((5,5),(5,5)) := by
  jgl_words
#print axioms plus

theorem product : value ((60053925,1891194216),(2090430923,260852809)) *
    value ((839969315,1393507838),(1451026085,492151165)) =
    value ((1458369550,1316359454),(1385711809,768552005)) := by
  jgl_words
#print axioms product

theorem difference : value ((1,2),(3,4))-value ((4,3),(2,1))=value ((2147483644,2147483646),(1,3)) := by
  jgl_words
#print axioms difference
end AspisR1.JGl_WordPreflight
