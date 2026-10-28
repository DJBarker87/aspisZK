import R1Z.ProverRwQueryWindow
import R1Z.ProverRwQueryDecode
set_option autoImplicit false
namespace R1Z.ProverRwQuerySourceWindow
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan ProverRwQueryWord
open ProverRwQueryWindow ProverRwQueryTransition ProverRwQueryDecode
open Query31ExplicitScanBody
open AspisR1QueryScanUnrolled.r0_transcript

def run (blocks advances : Blocks) (s : CurrentScan) : Result Output :=
  host_transcript.scan_query_words blocks advances s.accepted s.accepted_len s.draws

def blockWord (blocks : Blocks) (k : Nat) (hk : k<8) (i : Nat) : U32 :=
  queryMaskWord (blockRankWord (blocks.val[k]'(by simpa [blocks.property] using hk)) i)

theorem window_source (blocks advances : Blocks) (k fuel i : Nat) (s : CurrentScan)
    (hk : k<8) (hpart : i+fuel=8) (hd : s.draws.val=8*k+i)
    (hlen : s.accepted_len.val≤22) :
    run blocks advances s = (do
      let p ← window (blockWord blocks k hk) fuel i s
      run blocks advances p.2) := by
  induction fuel generalizing i s with
  | zero => rfl
  | succ fuel ih =>
    by_cases full : s.accepted_len=22#usize
    · simp only [window,full,if_true,bind_tc_ok]
    · have id : i<8 := by omega
      have db : s.draws.val<64 := by omega
      have cap : s.draws≠64#usize := by intro he; have hv:=congrArg UScalar.val he; change s.draws.val=64 at hv; omega
      have active : s.accepted_len.val<22 := by
        have ne : s.accepted_len.val≠22 := by intro he; apply full; exact UScalar.eq_of_val_eq he
        omega
      obtain ⟨ki,hki,hkiv⟩ := UScalar.div_spec s.draws (y:=8#usize) (by decide)
      have kval : ki.val=k := by change ki.val=s.draws.val/8 at hkiv; omega
      have remval : s.draws.val%8=i := by omega
      have read := read_closed blocks ki s.draws (by omega)
      simp only [kval,remval] at read
      change readWord blocks ki s.draws=ok (blockWord blocks k hk i) at read
      obtain ⟨next,hn,hnlen,hndraw,_⟩ := advance_q22 s (blockWord blocks k hk i) active db
      have tail := ih (i+1) next (by omega) (by omega) hnlen
      change host_transcript.scan_query_words blocks advances s.accepted s.accepted_len s.draws = _
      rw [source_factored]
      simp only [factored,full,cap,if_false,hki,read,hn,bind_tc_ok,window,bind_assoc_eq]
      exact tail

#print axioms window_source
end R1Z.ProverRwQuerySourceWindow
