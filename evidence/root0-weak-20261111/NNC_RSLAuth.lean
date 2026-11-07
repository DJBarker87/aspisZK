import NNC_WriteFree
import NNC_SnapshotRep
import NMS_RSLStepFacts
set_option autoImplicit false
namespace NNC_RSLAuth
open RSL RSL.TX2_241 NMS_RSLRefine

theorem lift_return {A : Type} (m : Spec A) (env : Env) (a : A) (events : List Event)
 (run : RS.lift m env ⟨.ret (.ok a),events⟩) : m env ⟨.ret a,events⟩ := by
 unfold RS.lift Spec.map at run
 obtain ⟨a',e1,e2,hm,hp,he⟩ := NMV_RslLaws.bind_return _ _ _ _ _ run
 simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Except.ok.injEq] at hp
 rcases hp with ⟨rfl,rfl⟩
 simpa only [he,List.append_nil] using hm

/-- Isolated post-verify suffix. Exact Result and event prefix; no account
or byte buffer is normalized. This is accepted-reference inversion only. -/
theorem successful (V : V2Lib) (m : Spec (Except V.VErr Unit)) (tail : RS Unit)
 (env : Env) (events : List Event)
 (run : RS.bind (RS.lift m) (fun r=>RS.seq (mapVErr V r) tail)
  env ⟨.ret (.ok ()),events⟩) :
 ∃ verifyEvents, m env ⟨.ret (.ok ()),verifyEvents⟩ := by
 obtain ⟨reply,verifyEvents,_,auth,h,_⟩ := rsbind_return _ _ _ _ _ run
 obtain ⟨_,_,_,mapped,_,_⟩ := rsbind_return _ _ _ _ _ h
 have replyOk : reply=.ok () := by
  cases reply with
  | ok u => cases u; rfl
  | error error =>
   unfold mapVErr at mapped
   obtain ⟨_,_,_,_,impossible,_⟩ := rsbind_return _ _ _ _ _ mapped
   cases congrArg Obs.exit impossible
 rw [replyOk] at auth
 exact ⟨verifyEvents,lift_return m env (.ok ()) verifyEvents auth⟩

/-- The OWN input domain and successful weak law are outputs of inversion,
not assumptions about a child's return. -/
theorem call (V : V2Lib) (pub proof ck : Bytes) (tail : RS Unit)
 (env : Env) (events : List Event)
 (run : RS.bind (RS.lift (Spec.call (Dom064 V)
  (fun x=>V.tx2auth x.1 x.2.1 x.2.2) (pub,proof,ck)))
  (fun r=>RS.seq (mapVErr V r) tail) env ⟨.ret (.ok ()),events⟩) :
 ∃ verifyEvents, Dom064 V (pub,proof,ck) ∧
  V.tx2auth pub proof ck env ⟨.ret (.ok ()),verifyEvents⟩ :=
 successful V _ tail env events run
#print axioms lift_return
#print axioms successful
#print axioms call
end NNC_RSLAuth
