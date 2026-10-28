import PV_L2C_DigestRoundtrip
import PV_L2C_AccountOrigins
set_option autoImplicit false
namespace PV_L2C_AccountEncode
open Aeneas Aeneas.Std Result R0Z.WriterRefine PV_L2C_DigestList

theorem decoded (ds : List Digest) (hc : ∀ d ∈ ds, Canon8 d) :
    run (ds.map PV_L2C_DigestEncode.encode) = ok (.Ok ds) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [List.map_cons,run,PV_L2C_DigestRoundtrip.decode d (hc d (by simp))]
    simp only [bind_tc_ok]
    rw [ih (by intro v hv;exact hc v (by simp [hv]))]
    rfl
#print axioms decoded

def tree (root : Digest) (frontier : Array Digest 20#usize)
    (hr : Canon8 root) (hf : ∀ j : Fin 20, Canon8 frontier.val[j.val]!) :
    PV_L2C_AccountOrigins.Tree root frontier where
  bytes := (root::List.ofFn (fun j : Fin 20 => frontier.val[j.val]!)).map PV_L2C_DigestEncode.encode
  decoded := root::List.ofFn (fun j : Fin 20 => frontier.val[j.val]!)
  count := by simp
  success := decoded _ (by
    intro d hd
    rcases List.mem_cons.mp hd with he | ht
    · subst d;exact hr
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht;exact hf j)
  root_field := rfl
  frontier_fields := by
    intro j
    simp only [List.getElem?_cons_succ,List.getElem?_ofFn,dif_pos j.isLt]
#print axioms tree
end PV_L2C_AccountEncode
