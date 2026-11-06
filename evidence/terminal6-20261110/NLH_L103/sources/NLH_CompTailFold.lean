import NLH_CompGather0
import NLH_CompGather1
import NLH_CompGather2
import NLH_CompGather3
import NLH_CompSelectors
import NLH_CompPoseidonSelectors
import NLH_CompPoseidon
import NLH_CompSemantic
import NLH_CompH1
import NLH_CompVariant
import NLH_CompCopy
import NLH_CompPrepared
import NLH_CompHornerLoop
import NLH_HornerTrace
import NLH_CompG
import NLH_FoldAppend
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompTailFold
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public)
open pool_v1.pair_forest_semantic_terminal
def headOrder : List Event := (List.finRange 4).map Event.gather ++
 [.selectors,.poseidonSelectors,.poseidon,.semantic,.h,.variant,.copy,.prepare]
def loopOrder : List Event := (List.finRange 28).map Event.horner
def order : List Event := headOrder ++ loopOrder ++ [.g]
/-- Entered237 tail: every child and frame is built inside this theorem.
The generic pre-state is overwritten only at its actual source assignments. -/
theorem source (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (base : State) (hd : NKR_DigestChildren.Domain pub)
 (hc : canonical claims) (hp : canonical point) (hl : Canon lambda) (hchi : Canon chi) (ht : Canon theta)
 (asset : pub.asset_id.val < 2147483647)
 (amount : (core.option.Option.unwrap_or pub.withdrawal_amount 0#u32).val < 2147483647) :
 ∃ final : State,NLH_RustCuts.Cuts (step pub claims point lambda chi theta) order base (ok (.Ok final)) order ∧
 NLH_TermComposeTail.run pub claims point lambda chi theta=ok (.Ok (returned final)) ∧
 Canon final.composition ∧ canonical final.openings.z ∧ canonical final.mask ∧
 Canon final.g ∧ Canon final.h ∧ Canon final.copy.active := by
 obtain ⟨p,_⟩ := NKR_TermGatherPoseidon.source claims point hc hp
 let a := NLH_CompGathers.stage p base 4
 let b : State := {a with selectors := p.selectors}
 let c : State := {b with poseidonSelectors := p.poseidonSelectors}
 let d : State := {c with poseidon := p.poseidon}
 have sSelectors := NLH_CompSelectors.selectors pub claims point lambda chi theta p a
 have sPoseidonSelectors := NLH_CompPoseidonSelectors.poseidon_selectors pub claims point lambda chi theta p b rfl
 have sPoseidon := NLH_CompPoseidon.step pub claims point lambda chi theta p c rfl rfl
 obtain ⟨semantic,sSemantic,cs,semanticCall⟩ := NLH_CompSemantic.source pub claims point lambda chi theta d hd
   p.zCanonical p.succCanonical p.xorCanonical p.selectorHigh p.selectorLow asset amount
 let e : State := {d with semantic := semantic}
 obtain ⟨h,sH,ch,hCall⟩ := NLH_CompH1.source pub claims point lambda chi theta e hc
 let f : State := {e with h := h}
 let g : State := {f with copyVariant := NLH_TermComposeTail.variant pub.variant}
 have sVariant := NLH_CompVariant.source pub claims point lambda chi theta f
 obtain ⟨copy,sCopy,cr,ca,copyCall⟩ := NLH_CompCopy.source pub claims point lambda chi theta g
   p.zCanonical ch p.selectorHigh p.selectorLow hl hchi
 let hstate : State := {g with copy := copy}
 obtain ⟨prepared,sPrepared,domain,preparedCall⟩ := NLH_CompPrepared.source pub claims point lambda chi theta hstate ht
 let preparedState : State := {hstate with prepared := prepared,composition := copy.residual, remaining := semantic.val.reverse ++ p.poseidon.val.reverse}
 have shape : ∀ ev∈loopOrder,∃ i,ev=Event.horner i := by
   intro ev mem
   obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
   exact ⟨i,rfl⟩
 have length : loopOrder.length=preparedState.remaining.length := by
   change ((List.finRange 28).map Event.horner).length=(semantic.val.reverse++p.poseidon.val.reverse).length
   simp only [List.length_map,List.length_finRange,List.length_append,List.length_reverse,semantic.property,p.poseidon.property]
   rfl
 have remainingCanonical : ∀ x∈preparedState.remaining,Canon x := by
   intro x hx
   rcases List.mem_append.mp hx with left|right
   · exact cs x (List.mem_reverse.mp left)
   · exact p.poseidonCanonical x (List.mem_reverse.mp right)
 obtain ⟨composition,loops,cc,trace⟩ := NLH_CompHornerLoop.source pub claims point lambda chi theta loopOrder preparedState
   shape length ht cr remainingCanonical domain
 let beforeG : State := {preparedState with composition := composition,remaining := []}
 obtain ⟨gv,sG,cg,gCall⟩ := NLH_CompG.source pub claims point lambda chi theta beforeG hc
 let final : State := {beforeG with g := gv}
 have head : NLH_RustCuts.Cuts (step pub claims point lambda chi theta) headOrder
   (NLH_CompGathers.stage p base 0) (ok (.Ok preparedState)) headOrder := by
   change NLH_RustCuts.Cuts _ [Event.gather 0,Event.gather 1,Event.gather 2,Event.gather 3,Event.selectors,Event.poseidonSelectors,
     Event.poseidon,Event.semantic,Event.h,Event.variant,Event.copy,Event.prepare] _ _ _
   exact .next (NLH_CompGather0.step pub claims point lambda chi theta p base)
    (.next (NLH_CompGather1.step pub claims point lambda chi theta p base)
     (.next (NLH_CompGather2.step pub claims point lambda chi theta p base)
      (.next (NLH_CompGather3.step pub claims point lambda chi theta p base)
       (.next sSelectors (.next sPoseidonSelectors (.next sPoseidon (.next sSemantic
        (.next sH (.next sVariant (.next sCopy (.next sPrepared (.nil preparedState))))))))))))
 have start : NLH_CompGathers.stage p base 0=base := by rfl
 rw [start] at head
 have endCut : NLH_RustCuts.Cuts (step pub claims point lambda chi theta) [.g] beforeG (ok (.Ok final)) [.g] :=
   .next sG (.nil final)
 have complete : NLH_RustCuts.Cuts (step pub claims point lambda chi theta) order base (ok (.Ok final)) order :=
   NLH_FoldAppend.rust (NLH_FoldAppend.rust head loops) endCut
 obtain ⟨oldPrepared,middle,oldOut,newCall,_,first,second,bodyCall,_⟩ :=
   NLH_TermHornerCut.source semantic p.poseidon theta copy.residual cs p.poseidonCanonical ht cr
 have samePrepared : oldPrepared=prepared := Result.ok.inj (newCall.symm.trans preparedCall)
 subst oldPrepared
 have sameOut : composition=oldOut := NLH_HornerTrace.unique trace (NLH_HornerTrace.append first second)
 have body : FIv_FoldsTotal.body semantic p.poseidon theta copy.residual=ok composition := by
   rw [sameOut];exact bodyCall
 have horner : NKR_TermHorner.run claims p.z p.mask semantic p.poseidon theta h copy=
     ok (composition,p.z,p.mask,gv,h,copy.active) := by
   simp only [NKR_TermHorner.run,body,NKR_TermHorner.column,gCall,bind_tc_ok]
 have sourceCall : NLH_TermComposeTail.run pub claims point lambda chi theta=ok (.Ok (returned final)) := by
   unfold NLH_TermComposeTail.run
   rw [p.gather0,bind_tc_ok,p.gather1,bind_tc_ok,p.gather2,bind_tc_ok,p.gather3,bind_tc_ok,
     p.selectorCall,bind_tc_ok,p.poseidonSelectorCall,bind_tc_ok,p.poseidonCall,bind_tc_ok,
     semanticCall,bind_tc_ok,NLH_TermComposeTail.hcolumn,bind_tc_ok,hCall,bind_tc_ok,
     NLH_TermComposeTail.variant_source,bind_tc_ok,copyCall,bind_tc_ok]
   have mapped : (do let out ← NKR_TermHorner.run claims p.z p.mask semantic p.poseidon theta h copy
                    ok (core.result.Result.Ok out : core.result.Result NKR_TermTail.Carrier NKR_TermTail.Error))=
      ok (.Ok (composition,p.z,p.mask,gv,h,copy.active)) := by rw [horner,bind_tc_ok]
   simp only [NKR_TermHorner.run,FIv_FoldsTotal.body,bind_assoc_eq,bind_tc_ok] at mapped
   simpa only [returned,FIq_Native.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
     core.iter.traits.iterator.Iterator.rev.trait_default,core.iter.traits.iterator.Iterator.rev.default,bind_tc_ok] using mapped
 exact ⟨final,complete,sourceCall,cc,p.zCanonical,p.maskCanonical,cg,ch,ca⟩
#print source
#print axioms source
end AspisR1.NLH_CompTailFold
end
