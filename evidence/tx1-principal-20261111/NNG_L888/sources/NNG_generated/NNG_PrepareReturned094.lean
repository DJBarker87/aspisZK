import NNG_PrepareFacts094
import NNG_PrepareGraph094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PrepareReturned094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Carriers094

theorem returned (a : NNG_PrepareInput087.Args) (env : RSL.Env)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a none)
 (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (native : NNG_PrepareAdapter094.call env (NNG_PrepareTransport094.digest env) (fromT9 a.public_)
  (NNG_Data137.bytes a.proof) () none (arr fromT3 a.g)=ok (.Ok p,g)) :
 ∃ input ev,LIBC_PreparedLaw.law input env ⟨.ret (.ok (toT12 p),arr toT3 g),ev⟩ ∧
 NGC_PreparationBoundary.Fields (NFW_PreparedPort.prepared (toT12 p)) ∧
 ∃ root0 root1,(toT12 p).roots=Array.make 2#usize [root0,root1] ∧
 root0.val=((NNG_PrepareInput087.input a none env).bytes.val.drop 16).take 32 := by
 rw [NNG_PrepareTransport094.call] at native
 cases run : NMP_Emitted.prepare (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a none env) with
 | fail e=>rw [run] at native;cases native
 | div=>rw [run] at native;cases native
 | ok reply=>
  rw [run] at native
  have equal : NNG_PrepareAdapter094.output reply=(.Ok p,g) := Result.ok.inj native
  rcases reply with ⟨r,mg⟩
  cases r with
  | Err e=>cases congrArg Prod.fst equal
  | Ok mp=>
   have same := (congrArg NNG_PrepareTransport094.port equal).symm.trans
    (NNG_PrepareTransport094.output (.Ok mp,mg))
   have samep : toT12 p=NNG_PrepareCarriers087.prepared mp := Except.ok.inj (congrArg Prod.fst same)
   have sameg : arr toT3 g=NMT_Transport.arr NNG_PrepareCarriers087.wide mg := congrArg Prod.snd same
   have facts := NNG_PrepareFacts094.returned a none env domain mp mg run
   rw [←samep,←sameg] at facts
   exact facts
#print axioms returned
end AspisR1.NNG_PrepareReturned094
