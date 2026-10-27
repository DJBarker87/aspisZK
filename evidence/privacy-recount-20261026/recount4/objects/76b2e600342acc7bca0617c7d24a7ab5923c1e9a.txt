import R1Z.ProverRwQueryListStep
set_option autoImplicit false
namespace R1Z.ProverRwQueryWindow
open Aeneas Aeneas.Std Result ProverRwQueryTransition ProverRwQueryListStep
open Query31ExplicitScanBody
open Query31ExplicitListLoop (validState validState_of_bounds listNext scanListLoop optionStop step)

def window (word : Nat → U32) : Nat → Nat → CurrentScan → Result (Bool × CurrentScan)
  | 0,_,s => ok (false,s)
  | fuel+1,i,s =>
    if s.accepted_len=22#usize then ok (true,s)
    else if s.draws=64#usize then ok (true,s)
    else do let next ← advance s (word i); window word fuel (i+1) next

theorem list_window (word : Nat → U32) (fuel i : Nat) (s : CurrentScan)
    (hlen : s.accepted_len.val≤22) (bound : s.draws.val+fuel≤64) :
    (do let (sf,pending) ← scanListLoop ((List.range' i fuel).map word) s
        ok (optionStop pending,sf)) = window word fuel i s := by
  induction fuel generalizing i s with
  | zero =>
    unfold scanListLoop step
    rw [Aeneas.Std.loop.eq_def]
    simp only [List.range'_zero,List.map_nil,body,stdOps,listNext,bind_tc_ok,window]
    rfl
  | succ fuel ih =>
    rw [List.range'_succ,List.map_cons]
    by_cases full : s.accepted_len=22#usize
    · unfold scanListLoop step
      rw [Aeneas.Std.loop.eq_def]
      simp only [body,stdOps,listNext,bind_tc_ok,full,if_true,window]
      rfl
    · by_cases cap : s.draws=64#usize
      · unfold scanListLoop step
        rw [Aeneas.Std.loop.eq_def]
        simp only [body,stdOps,listNext,bind_tc_ok,full,if_false,cap,if_true,window]
        rfl
      · have active : s.accepted_len.val<22 := by
          have ne : s.accepted_len.val≠22 := by intro he; apply full; exact UScalar.eq_of_val_eq he
          omega
        have hd : s.draws.val<64 := by omega
        obtain ⟨next,hn,hnlen,hndraw,_⟩ := advance_q22 s (word i) active hd
        have hb := body_advance s (word i) ((List.range' (i+1) fuel).map word) active hd
        rw [hn,bind_tc_ok] at hb
        have hloop : scanListLoop (word i :: (List.range' (i+1) fuel).map word) s =
            scanListLoop ((List.range' (i+1) fuel).map word) next := by
          unfold scanListLoop step
          rw [Aeneas.Std.loop.eq_def]
          simp only [hb]
        rw [hloop,ih (i+1) next hnlen (by omega)]
        simp only [window,full,cap,if_false,hn,bind_tc_ok]

theorem window_total (word : Nat → U32) (fuel i : Nat) (s : CurrentScan)
    (hlen : s.accepted_len.val≤22) (bound : s.draws.val+fuel≤64) :
    ∃ stop sf, window word fuel i s=ok (stop,sf) ∧ validState sf ∧
      (stop=true → sf.accepted_len=22#usize ∨ sf.draws=64#usize) ∧
      (stop=false → sf.draws.val=s.draws.val+fuel) ∧
      s.draws.val≤sf.draws.val ∧ sf.draws.val≤s.draws.val+fuel := by
  induction fuel generalizing i s with
  | zero => exact ⟨false,s,rfl,validState_of_bounds s hlen (by omega),by simp,by simp,by omega,by omega⟩
  | succ fuel ih =>
    by_cases full : s.accepted_len=22#usize
    · exact ⟨true,s,by simp only [window,full,if_true],validState_of_bounds s hlen (by omega),by intro _; exact Or.inl full,by simp,by omega,by omega⟩
    · by_cases cap : s.draws=64#usize
      · exact ⟨true,s,by simp only [window,full,if_false,cap,if_true],validState_of_bounds s hlen (by omega),by intro _; exact Or.inr cap,by simp,by omega,by omega⟩
      · have active : s.accepted_len.val<22 := by
          have ne : s.accepted_len.val≠22 := by intro he; apply full; exact UScalar.eq_of_val_eq he
          omega
        obtain ⟨next,hn,hnlen,hndraw,_⟩ := advance_q22 s (word i) active (by omega)
        obtain ⟨stop,sf,hr,hv,ht,hf,hl,hu⟩ := ih (i+1) next hnlen (by omega)
        exact ⟨stop,sf,by simp only [window,full,cap,if_false,hn,bind_tc_ok,hr],hv,ht,
          by intro hs; have hh:=hf hs; omega,by omega,by omega⟩

#print axioms list_window
#print axioms window_total
end R1Z.ProverRwQueryWindow
