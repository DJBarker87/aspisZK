import R1Z.PV_CBL_SplitModel
namespace R1Z.PV_CBL_SplitRecompose
set_option autoImplicit false

/-- A single byte-copy block followed by the unread suffix is exactly the
suffix before that block. No byte normalization or fixed-bound expansion. -/
theorem one {T : Type} (src : List T) (size i : Nat) :
    PV_CBL_SplitModel.block src size i ++ src.drop ((i+1)*size) =
      src.drop (i*size) := by
  unfold PV_CBL_SplitModel.block
  have h : (i+1)*size=i*size+size := by omega
  rw [h,←List.drop_drop]
  exact List.take_append_drop size (src.drop (i*size))

theorem prefix_tail {T : Type} (src : List T) (size : Nat) :
    src.take ((src.length/size)*size) ++ PV_CBL_SplitModel.tail src size=src := by
  exact List.take_append_drop _ _

#print axioms one
#print axioms prefix_tail
end R1Z.PV_CBL_SplitRecompose
