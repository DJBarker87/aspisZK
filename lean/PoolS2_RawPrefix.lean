import PoolS2_RawSnapshot
import PoolS2_PrefixKeys
set_option autoImplicit false
namespace AspisR1.PoolS2_RawPrefix
open Aeneas Aeneas.Std Result S2W_D189Entry PoolS2_Prefix

theorem roles (e : Entry) (data : Slice U8) (r : Roles)
    (h : run (PoolS2_RawSnapshot.accounts e) data = ok (.Ok r)) :
    r.master = PoolS2_RawSnapshot.snapshot e 0 ∧
    r.checkpoint = PoolS2_RawSnapshot.snapshot e 9 ∧
    r.payer = PoolS2_RawSnapshot.snapshot e 10 ∧
    r.system = PoolS2_RawSnapshot.snapshot e 11 := by
  have selected := (PoolS2_PrefixCuts.accepted _ data r h).2.2.2.1
  have cuts := PoolS2_SelectCuts.accepted _ r selected
  exact ⟨Result.ok.inj (cuts.1.symm.trans (PoolS2_RawSnapshot.indexed e 0#usize (by decide))),
    Result.ok.inj (cuts.2.2.1.symm.trans (PoolS2_RawSnapshot.indexed e 9#usize (by decide))),
    Result.ok.inj (cuts.2.2.2.1.symm.trans (PoolS2_RawSnapshot.indexed e 10#usize (by decide))),
    Result.ok.inj (cuts.2.2.2.2.symm.trans (PoolS2_RawSnapshot.indexed e 11#usize (by decide)))⟩

theorem data_cells (e : Entry) (data : Slice U8) (r : Roles)
    (h : run (PoolS2_RawSnapshot.accounts e) data = ok (.Ok r)) :
    (e.heap.accounts 0).1 ≠ (e.heap.accounts 9).1 := by
  have different := PoolS2_PrefixKeys.master_checkpoint _ data r h
  obtain ⟨master,checkpoint,_,_⟩ := roles e data r h
  intro same
  change (e.handles 0).1 = (e.handles 9).1 at same
  have sameSnapshot := PoolS2_RawSnapshot.cell_alias e 9 0 same.symm
  exact different (congrArg (fun a : AdapterRw.Cuts.Account => a.key)
    (checkpoint.trans (sameSnapshot.trans master.symm)))

#print axioms roles
#print axioms data_cells
end AspisR1.PoolS2_RawPrefix
