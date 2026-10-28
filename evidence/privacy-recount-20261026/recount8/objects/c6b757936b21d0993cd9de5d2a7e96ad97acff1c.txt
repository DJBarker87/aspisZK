import R1Z.PV_CompressList
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CompressSuffix
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6CompressControl
variable [ExternalTypes] [ExternalFuns]

theorem read (values : Slice M) (i : Usize) (h : i.val < values.val.length) :
    Slice.index_usize values i = ok values.val[i.val] := by
  simp only [Slice.index_usize,Slice.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem h]

theorem step (values : Slice M) (i : Usize) (h : i.val < (Slice.len values).val) :
    (Usize.wrapping_add i 1#usize).val = i.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  change (i.val+1)%UScalar.size .Usize=i.val+1
  apply Nat.mod_eq_of_lt
  have big := (Slice.len values).hSize
  omega

theorem finite (values : Slice M) (lambda : Q) (fuel : Nat)
    (out power : Q) (i : Usize) (bound : i.val+fuel=(Slice.len values).val) :
    ProverRwP6CompressControl.finite values lambda fuel out power i =
      PV_CompressList.fold (values.val.drop i.val) lambda out power := by
  induction fuel generalizing out power i with
  | zero =>
    have hi : ¬i < Slice.len values := by
      change ¬ i.val < (Slice.len values).val
      omega
    have hn : values.val.drop i.val = [] := List.drop_eq_nil_of_le (by
      change values.val.length ≤ i.val
      change i.val+0=values.val.length at bound
      omega)
    simp only [ProverRwP6CompressControl.finite,dispatch,hi,if_false,hn,PV_CompressList.nil]
  | succ fuel ih =>
    have hi : i.val < (Slice.len values).val := by omega
    have hs := step values i hi
    have hl : i.val < values.val.length := hi
    rw [List.drop_eq_getElem_cons hl,PV_CompressList.cons]
    simp only [ProverRwP6CompressControl.finite,dispatch,
      show i < Slice.len values from hi,if_true,read values i hl,bind_tc_ok]
    repeat' first | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro _ _
    rw [ih _ _ _ (by omega),hs]
#print axioms read
#print axioms step
#print axioms finite
end R1Z.PV_CompressSuffix
