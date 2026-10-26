import R1Z.PV_L2_F6Pivot
import R1Z.PV_L2_F6Image
import R1Z.PV_L2_F6Product
set_option autoImplicit false
namespace R1Z.PV_L2_F6Callers
open Aeneas Aeneas.Std Result R1CertCheck R1Z.PV_L2_Record

def piv (idx : Slice U32) (io s : Usize) (lane : Slice U32) (lj : U32) :=
  PV_L2_F6Pivot.loop idx io s lane lj s.val true 0#usize
theorem piv_erases (idx : Slice U32) (io s : Usize) (lane : Slice U32) (lj : U32) :
    (piv idx io s lane lj).value = piv_ok idx io s lane lj :=
  PV_L2_F6Pivot.piv_erases idx io s lane lj

def image (m : Slice U32) (st nrows j : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co s : Usize) (tgt : Slice U32) (to1 ts : Usize) :=
  PV_L2_F6Image.loop m st nrows j idx io c co s tgt to1 ts nrows.val true 0#usize
theorem image_erases (m : Slice U32) (st nrows j : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co s : Usize) (tgt : Slice U32) (to1 ts : Usize) :
    (image m st nrows j idx io c co s tgt to1 ts).value =
      kimg_ok m st nrows j idx io c co s tgt to1 ts :=
  PV_L2_F6Image.image_erases m st nrows j idx io c co s tgt to1 ts

def product (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co ni nj len : Usize) :=
  PV_L2_F6Product.loop a ao b bo c co ni nj len ni.val true 0#usize
theorem product_erases (a : Slice U32) (ao : Usize) (b : Slice U32) (bo : Usize)
    (c : Slice U32) (co ni nj len : Usize) :
    (product a ao b bo c co ni nj len).value = prod_ok a ao b bo c co ni nj len :=
  PV_L2_F6Product.product_erases a ao b bo c co ni nj len

#print axioms piv_erases
#print axioms image_erases
#print axioms product_erases
end R1Z.PV_L2_F6Callers
