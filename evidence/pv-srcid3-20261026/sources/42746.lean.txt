import R1Z.PV_Src_CanonicalRoots
import R1Z.PV_RunJoin_RootModelTable
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_RootFieldMeaning
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap

theorem source (l : Fin 21) :
    (fun i : Fin 8 => liftU (K := ZMod 2147483647) (PV_Src_CanonicalRoots.table.val[l.val]!).val[i.val]!) =
      AspisR1.AppendNode.frozenEmpty l := by
  funext i
  rw [PV_Src_CanonicalRoots.at_level,arr8_get _ i.val i.isLt]
  simp only [PV_Src_CanonicalRoots.word,liftU,UScalar.ofNatCore_val_eq,AspisR1.AppendNode.frozenEmpty]

#print axioms source
end R1Z.PV_Src_RootFieldMeaning
