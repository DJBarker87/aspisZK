import NDO_JFw_TX2_Coefficients
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_PowerReads
open Aeneas Aeneas.Std Result

theorem source (j : Fin 29) :
    Array.index_usize JFr_TX2_FirstLane.native
      (Usize.ofNat j.val (by have:=j.isLt;scalar_tac))=ok (JFw_TX2_Coefficients.value j) := by
  obtain ⟨x,run,same⟩ := WP.spec_imp_exists
    (Array.index_usize_spec JFr_TX2_FirstLane.native
      (Usize.ofNat j.val (by have:=j.isLt;scalar_tac))
      (by change _<JFr_TX2_FirstLane.native.val.length;rw [JFr_TX2_FirstLane.native.property];scalar_tac))
  rw [same] at run
  have cv : (Usize.ofNat j.val (by have:=j.isLt;scalar_tac)).val=j.val := by scalar_tac
  simp only [cv] at run
  have run' : Array.index_usize JFr_TX2_FirstLane.native
      (Usize.ofNat j.val (by have:=j.isLt;scalar_tac))=ok (JFw_TX2_PowersExplicit.entry j) := by
    simpa only [JFr_TX2_FirstLane.native,FIp_DotsAdapter.toArray,List.getElem_map,
      JFw_TX2_PowersExplicit.entry] using run
  rw [JFw_TX2_Coefficients.source] at run'
  exact run' 
#print axioms source
end AspisR1.JFw_TX2_PowerReads
end
