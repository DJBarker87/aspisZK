import NCP_HelperExtracted.Funs
import NCP_CallerDomains
set_option autoImplicit false
noncomputable section
namespace NCP_CanonReference
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem source (d : Array U32 8#usize) :
    NCP_HelperExtracted.NCP_refs.NCP_canon d =
      pool_v1.pair_tree_profile.digest_is_canonical d := by
  obtain ⟨a,b,c,e,f,g,h,i,same⟩ := NBG_Utilities.shape d
  subst d
  rw [NBD_DigestInduction.source]
  simp [NCP_HelperExtracted.NCP_refs.NCP_canon,Array.index_usize,
    NBG_Utilities.pack,Array.make,NBD_DigestInduction.Canonical,Fin.forall_fin_succ]
  split_ifs <;> simp_all

#print axioms source
end NCP_CanonReference
