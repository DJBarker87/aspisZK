import NNU_MerkleHead
import NNU_OffsetArithmetic
import F3Q_VerifyGuards
set_option autoImplicit false
namespace AspisR1.NOM_MerkleGuard
open Aeneas Aeneas.Std Result MultiproofConeRef

/-- Inversion of the extracted valid_indices scan (converse of
NNU_MerkleValidity.indices): an accepted scan from i reads only canonical
indices and strictly ascending adjacent pairs from i-1 on. -/
theorem scan (idx : Array U32 16#usize) (n : Usize) (bounded : n.val ≤ 16) (fuel : Nat) :
 ∀ (i : Usize), n.val - i.val ≤ fuel → reference.valid_indices idx n i = .ok true →
 (∀ j, i.val ≤ j → j < n.val → idx.val[j]!.val < 262144) ∧
 (∀ j, i.val ≤ j + 1 → j + 1 < n.val → idx.val[j]!.val < idx.val[j+1]!.val) := by
 induction fuel with
 | zero =>
   intro i enough _
   exact ⟨fun j h1 h2 => by omega, fun j h1 h2 => by omega⟩
 | succ fuel ih =>
   intro i enough run
   rw [reference.valid_indices] at run
   by_cases stop : i ≥ n
   · have stop' : i.val ≥ n.val := stop
     exact ⟨fun j h1 h2 => by omega, fun j h1 h2 => by omega⟩
   · have active : i.val < n.val := by change ¬ i.val ≥ n.val at stop; omega
     have read := MultiproofConePhysicalPrelude.array_read idx i (by change i.val < 16; omega)
     simp only [stop, if_false, read, bind_tc_ok] at run
     by_cases big : idx.val[i.val]! ≥ 262144#u32
     · simp only [big, if_true] at run <;>
        first | exact absurd (Result.ok.inj run) (by decide) | cases run
     · have canon : idx.val[i.val]!.val < 262144 := by
         change ¬ idx.val[i.val]!.val ≥ 262144 at big
         omega
       have next_bound : i.val+1≤UScalar.cMax .Usize := by scalar_tac
       let ni := Usize.ofNat (i.val+1) next_bound
       have add : (i+1#usize : Result Usize)=.ok ni :=
         NNU_OffsetArithmetic.add _ _ _ (by rfl)
       simp only [big, if_false] at run
       by_cases positive : i>0#usize
       · have sub_bound : i.val-1≤UScalar.cMax .Usize := by scalar_tac
         let pi := Usize.ofNat (i.val-1) sub_bound
         have sub : (i-1#usize : Result Usize)=.ok pi :=
           NNU_OffsetSubtract.sub _ _ _ (by change 1 ≤ i.val; change i.val > 0 at positive; omega) (by rfl)
         simp only [positive, if_true, sub, bind_tc_ok,
           MultiproofConePhysicalPrelude.array_read idx pi (by change i.val-1 < 16; omega)] at run
         by_cases desc : idx.val[pi.val]! ≥ idx.val[i.val]!
         · simp only [desc, if_true] at run <;>
            first | exact absurd (Result.ok.inj run) (by decide) | cases run
         · have asc : idx.val[pi.val]!.val < idx.val[i.val]!.val := by
             change ¬ idx.val[pi.val]!.val ≥ idx.val[i.val]!.val at desc
             omega
           simp only [desc, if_false, add, bind_tc_ok] at run
           obtain ⟨c1, c2⟩ := ih ni (by change n.val-(i.val+1)≤fuel; omega) run
           refine ⟨?_, ?_⟩
           · intro j h1 h2
             by_cases hj : j = i.val
             · subst hj
               exact canon
             · exact c1 j (by change i.val + 1 ≤ j; omega) h2
           · intro j h1 h2
             by_cases hj : j + 1 = i.val
             · have e : j = pi.val := by change j = i.val - 1; omega
               subst e
               have e2 : pi.val + 1 = i.val := by change i.val - 1 + 1 = i.val; omega
               rw [e2]
               exact asc
             · exact c2 j (by change i.val + 1 ≤ j + 1; omega) h2
       · simp only [positive, if_false, add, bind_tc_ok] at run
         obtain ⟨c1, c2⟩ := ih ni (by change n.val-(i.val+1)≤fuel; omega) run
         have zero : i.val = 0 := by change ¬ i.val > 0 at positive; omega
         refine ⟨?_, ?_⟩
         · intro j h1 h2
           by_cases hj : j = i.val
           · subst hj
             exact canon
           · exact c1 j (by change i.val + 1 ≤ j; omega) h2
         · intro j h1 h2
           exact c2 j (by change i.val + 1 ≤ j + 1; omega) h2

/-- The owned verifier's own guards give the frozen-order well-formedness of
the live indices (converse direction of NNU_MerkleHead.source). -/
theorem well (s : reference.Scratch) (nonzero : s.n ≠ 0#usize) (bounded : ¬ s.n > 16#usize)
 (valid : reference.valid_indices s.idx s.n 0#usize = .ok true) :
 OraclePortFrozenOrder.wellFormed ((MultiproofConePhysicalViews.live s 0 s.n.val).map Prod.fst) := by
 have positive : 0 < s.n.val := by
   by_contra bad
   exact nonzero (UScalar.eq_of_val_eq (by change s.n.val=0; omega))
 have bound : s.n.val ≤ 16 := by change ¬ s.n.val > 16 at bounded; omega
 obtain ⟨canon, adj⟩ := scan s.idx s.n bound s.n.val 0#usize (by simp) valid
 have step : ∀ j, j + 1 < s.n.val →
   MultiproofConeLivePreservation.keys s j < MultiproofConeLivePreservation.keys s (j+1) :=
   fun j h => adj j (by simp) h
 have strict : MultiproofConeLiveOrder.Strict (MultiproofConeLivePreservation.keys s) 0 s.n.val := by
   unfold MultiproofConeLiveOrder.Strict
   intro a b _ ab bn
   induction b with
   | zero => omega
   | succ b ih =>
     by_cases e : a = b
     · subst e
       exact step a bn
     · have h1 := ih (by omega) (by omega)
       have h2 := step b bn
       omega
 have len : ((MultiproofConePhysicalViews.live s 0 s.n.val).map Prod.fst).length = s.n.val := by
   simp only [List.length_map, MultiproofConeRootGuard.live_length]
 refine ⟨?_, ?_, MultiproofConePhysicalViews.live_sorted s s.n.val strict, ?_⟩
 · intro empty
   have h := congrArg List.length empty
   rw [len, List.length_nil] at h
   omega
 · rw [len]
   exact bound
 · intro x mem
   obtain ⟨j, hj, hx⟩ := List.mem_iff_getElem.mp mem
   have hj' : j < s.n.val := lt_of_lt_of_eq hj len
   rw [← hx]
   simp only [MultiproofConePhysicalViews.live, MultiproofConePhysicalLive.view, List.map_map,
     List.getElem_map, List.getElem_range, Function.comp_apply,
     MultiproofConePhysicalViews.decodeEntry, MultiproofConePhysicalLive.cell, Nat.zero_add]
   exact canon j (by simp) hj'

theorem aligned (nodes : Slice U8) (multiple : Slice.len nodes % 32#usize = .ok 0#usize) :
 nodes.val.length % 32 = 0 := by
 obtain ⟨rem, rem_run, rem_value⟩ := WP.spec_imp_exists
   (UScalar.rem_spec (x:=Slice.len nodes) (y:=32#usize) (by decide))
 have r : rem = 0#usize := Result.ok.inj (rem_run.symm.trans multiple)
 subst r
 change 0 = nodes.val.length % 32 at rem_value
 omega

/-- Everything an accepted owned verifier run exposes, at ANY digest instance. -/
theorem guards {X : Type} (D : MultiproofConeRef.aspis_core.digest.Digest32 X) (hash : X)
 (root : Array U8 32#usize) (s out : reference.Scratch) (nodes : Slice U8)
 (accepted : reference.verify_owned D hash root s nodes = .ok (true,out)) :
 OraclePortFrozenOrder.wellFormed ((MultiproofConePhysicalViews.live s 0 s.n.val).map Prod.fst) ∧
 nodes.val.length % 32 = 0 ∧
 reference.levels D hash {s with «at»:=0#usize} nodes 18#u32 = .ok (.Done out) ∧
 MultiproofConeRootGuard.sourceRoot root nodes out = true := by
 have wrapper : MultiproofConeP6Verify.wrapper
   (fun t => reference.levels D hash t nodes 18#u32) root s nodes = .ok (true,out) := accepted
 obtain ⟨nonzero,bounded,valid,multiple⟩ := F3Q_VerifyGuards.accepted _ root s out nodes wrapper
 obtain ⟨run,rootOK⟩ := Port4B_VerifyInstall.wrapper_success _ root s out nodes wrapper
 exact ⟨well s nonzero bounded valid, aligned nodes multiple, run, rootOK⟩

#print axioms scan
#print axioms well
#print axioms aligned
#print axioms guards
end AspisR1.NOM_MerkleGuard
