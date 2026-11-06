import NLH_TermSemanticRoot
import NLH_SemanticPrefix
import NLH_DigestChain
import NLH_ScalarTail
import NLH_FoldAppend
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_SemanticFold
open Aeneas Aeneas.Std Result FIq_Native NLH_SemanticState
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public Openings Selectors)
open pool_v1.pair_forest_semantic_terminal
def initial : State := ⟨NKR_TermSemanticSource.zero,(fun _ => field.QM31.ZERO),
 (fun _ => field.QM31.ZERO),Array.repeat 2#usize field.QM31.ZERO⟩
/-- Complete source-order parent fold over the native window transcriptions.
Every child packet and field domain is instantiated internally at SAME inputs.
Native credit and candidate children remain conditional on the ledger gate. -/
theorem source (pub : Public) (o : Openings) (s : Selectors)
 (hd : NKR_DigestChildren.Domain pub) (hz : canonical o.z) (hs : canonical o.succ_z)
 (hx : canonical o.xor12_z) (hh : canonical s.high) (hl : canonical s.low)
 (asset : pub.asset_id.val < 2147483647)
 (amount : (core.option.Option.unwrap_or pub.withdrawal_amount 0#u32).val < 2147483647) :
 ∃ final : State,
 NLH_FoldCore.Cuts (step pub o s) order initial (ok final) order ∧
 run pub o s initial=ok final ∧ canonical final.packed ∧
 semantic_packed pub o s=ok final.packed ∧ NLH_TermSemanticRoot.reference pub o s=ok final.packed := by
 obtain ⟨p,digests,_,scalar,wrapper,cd,_,_,_,sameOut,direct,reference,parent⟩ :=
   NLH_TermSemanticRoot.source pub o s hd hz hs hx hh hl asset amount
 let beforeDigest := NLH_SemanticPrefix.stage p initial 4
 let afterDigest : State := {beforeDigest with digests := digests}
 have digestStep : step pub o s .digest beforeDigest=ok afterDigest := by
   change (do let d ← NKR_DigestWrapper.reference pub o s;ok {beforeDigest with digests := d})=_
   rw [wrapper,bind_tc_ok]
 obtain ⟨afterWrites,writes,written,cw,dframe,lframe,sframe⟩ :=
   NLH_DigestChain.source pub o s afterDigest p.canonical_occupancy cd
 have packed : afterWrites.packed=p.packedDigests := Result.ok.inj (written.symm.trans direct)
 have scalarStart : NLH_ScalarChain.stage scalar afterWrites 0=afterWrites := by
   unfold NLH_ScalarChain.stage
   have locals : NLH_ScalarDefs.snapshot scalar 0=afterWrites.locals := by
     funext j
     change (if j.val < 0 then NLH_ScalarDefs.values scalar j else field.QM31.ZERO)=afterWrites.locals j
     rw [if_neg (Nat.not_lt_zero _)]
     exact (congrFun lframe j).symm
   rw [locals]
 have fields := NLH_ScalarChain.fields scalar afterWrites
 rw [scalarStart] at fields
 let afterFields := NLH_ScalarChain.stage scalar afterWrites 12
 obtain ⟨final,tail,finished,_,_,_⟩ := NLH_ScalarTail.cuts scalar afterFields packed
   (NLH_ScalarChain.complete_locals scalar afterWrites)
 have headCuts := NLH_SemanticPrefix.cuts pub o s p initial
 have digestCuts := NLH_FoldCore.Cuts.next digestStep writes
 have total := NLH_FoldAppend.plain (NLH_FoldAppend.plain
   (NLH_FoldAppend.plain headCuts digestCuts) fields) tail
 have start : NLH_SemanticPrefix.stage p initial 0=initial := by rfl
 rw [start] at total
 have complete : NLH_FoldCore.Cuts (step pub o s) order initial (ok final) order := by
   simpa only [order,List.append_assoc] using total
 have out : final.packed=p.out := finished.trans sameOut
 refine ⟨final,complete,NLH_FoldCore.result complete,?_,?_,?_⟩
 · rw [out];exact p.canonical_out
 · rw [out];exact parent
 · rw [out];exact reference
#print source
#print axioms source
end AspisR1.NLH_SemanticFold
end
