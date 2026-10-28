import PV_L2C_WriterChainRange
import PV_L2C_AuxRange
set_option autoImplicit false
namespace PV_L2C_TraceRange
open Aeneas Aeneas.Std Result R0Z.WriterRefine PV_L2C_BlockRange

structure PublicWords (p : RustPublic) : Prop where
  asset : p.asset.val < 2147483647
  frontier : ∀ n, n < 20 → Canon8 (p.frontier.val[n]!)
  empty : ∀ n, n < 20 → Canon8 (p.empty.val[n]!)

variable (w : RustWitness) (p : RustPublic)
    (hw : R1Z.BuilderRecordCanonical.CanonicalWords w) (hp : PublicWords p)

theorem block (n : Nat) (hn : n < 57) : Canonical (blockR w p n) := by
  exact fallback _ _ (zeros 256#usize) (fun b hb =>
    PV_L2C_WriterChainRange.records w p hw hp.asset hp.frontier hp.empty n hn b hb)
#print axioms block

theorem cell (c : Fin 29) (r : Fin 1024) : (copyCell w p c r).val < 2147483647 := by
  unfold copyCell
  have hr := r.isLt
  split_ifs with hc hblock hpath
  · exact block w p hw hp (r.val/16) (by omega) _ (by simp;omega)
  · exact fallback (pathR w p) _ (zeros 1536#usize)
      (fun b hb => PV_L2C_AuxRange.path w p hw.shape b hb) _ (by simp;omega)
  · exact fallback (auxR w p) _ (zeros 256#usize)
      (fun b hb => PV_L2C_AuxRange.aux w p hw b hb) _ (by simp;omega)
  · change 0 < 2147483647;omega
#print axioms cell

theorem stable : Canonical (stableBank w p) := by
  intro k hk
  have hk' : k < 16384 := by simpa using hk
  rw [stableBank,arrT_get _ k hk']
  split_ifs
  · change 0 < 2147483647;omega
  · exact cell w p hw hp _ _
#print axioms stable

theorem late : Canonical (lateBank w p) := by
  intro k hk
  have hk' : k < 16384 := by simpa using hk
  rw [lateBank,arrT_get _ k hk']
  split_ifs with hl
  · unfold LateRow at hl
    exact block w p hw hp (k%1024/16) (by omega) _ (by simp;omega)
  · change 0 < 2147483647;omega
#print axioms late

theorem merge (stable late out : Array U32 16384#usize)
    (hs : Canonical stable) (hl : Canonical late)
    (hout : R0WriterCopies.merge_copy stable late = ok out) : Canonical out := by
  obtain ⟨expected,he,hcells⟩ := merge_copy_loop_spec stable late 16384 0#usize
    (Array.repeat 16384#usize 0#u32) (by scalar_tac)
  have he' : R0WriterCopies.merge_copy stable late = ok expected := by
    rw [R0WriterCopies.merge_copy];exact he
  have same : out = expected := Result.ok.inj (hout.symm.trans he')
  intro k hk
  rw [same,hcells,if_pos (show (0#usize : Usize).val ≤ k ∧ k < 16384 from ⟨by simp,by simpa using hk⟩)]
  split_ifs
  · exact hl k hk
  · exact hs k hk
#print axioms merge

theorem merged (c : Fin 29) (r : Fin 1024) :
    (copyCellMerged w p c r).val < 2147483647 := by
  unfold copyCellMerged
  split_ifs with hc
  · exact fallback (mergedR w p) _ (zeros 16384#usize)
      (fun b hb => merge _ _ b (stable w p hw hp) (late w p hw hp) hb) _
      (by have := r.isLt;simp;omega)
  · change 0 < 2147483647;omega
#print axioms merged
end PV_L2C_TraceRange
