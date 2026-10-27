import RPt_JFo_Prepared
import RPz7_Tx2N_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_Opening
open Aeneas Aeneas.Std Result

theorem source (i : Usize) (bound : i.val<22) :
    ∃ view, Port4B_Opening.opening JFx_NativeBytes.proof i=ok view ∧ view.val.length=832 ∧
      MultiproofConeCanonical.bytesOf view.val=OraclePortCompactDraft.slice
        (MultiproofConeCanonical.bytesOf JFx_NativeBytes.proof.val) (10055+i.val*832) 832 :=
  Port4B_Opening.opening_exact JFx_NativeBytes.proof JFx_NativeBytes.proofBytes_length i bound

def cursor (i : Fin 22) : Usize := Usize.ofNat i.val (by have := i.isLt;scalar_tac)
def value (i : Fin 22) : Slice U8 := Classical.choose (source (cursor i) i.isLt)
theorem call (i : Fin 22) : Port4B_Opening.opening JFx_NativeBytes.proof (cursor i)=ok (value i) :=
  (Classical.choose_spec (source (cursor i) i.isLt)).1
theorem length (i : Fin 22) : (value i).val.length=832 :=
  (Classical.choose_spec (source (cursor i) i.isLt)).2.1
theorem selected (i : Fin 22) : (value i).val=(JFx_NativeBytes.proof.val.drop (10055+i.val*832)).take 832 := by
  have cv : (cursor i).val=i.val := rfl
  apply MultiproofConeByteEquality.bytes_injective
  have h := (Classical.choose_spec (source (cursor i) i.isLt)).2.2
  simpa only [MultiproofConeCanonical.bytesOf,OraclePortCompactDraft.slice,
    List.map_take,List.map_drop,value,cv] using h

#print axioms call
#print axioms length
#print axioms selected
#print axioms source
end AspisR1.JFo_Opening
end
