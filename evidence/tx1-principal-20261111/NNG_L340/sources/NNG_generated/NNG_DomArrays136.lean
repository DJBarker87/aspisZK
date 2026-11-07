import NNG_DomMask136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomArrays136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_Transport
open NNG_TraceAll136 NNG_TypedDomains136 NNG_LIBScalar NNG_LIBArrayDomain NNG_LIBClaimsDomain

theorem blind {W : Type} (fallback : Value) (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (running terminal : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript Unit)
    (etaDom : Domain s.challenges.eta) (terminalDom : Domain terminal) (alphaDom : DomainArray alpha) (claimsDom : DomainClaims claims) :
    All Checked (NNG_TreeSuffixes.f_q c s running terminal alpha t1 claims (NNG_FromFnValues136.low claims) (NNG_FromFnValues136.high claims) (NNG_Array136.row0 claims)) := by
  have selected := NNG_Array136.index (NNG_Array136.row0 claims) 27#usize (by decide)
  unfold NNG_TreeSuffixes.f_q
  rw [selected]
  exact NNG_DomMask136.mask fallback c env source s p prefixEq running terminal alpha claims t1 etaDom terminalDom alphaDom claimsDom
#print axioms blind

theorem row0 {W : Type} (fallback : Value) (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (running terminal : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript Unit)
    (etaDom : Domain s.challenges.eta) (terminalDom : Domain terminal) (alphaDom : DomainArray alpha) (claimsDom : DomainClaims claims) :
    All Checked (NNG_TreeSuffixes.f_a2 c s running terminal alpha t1 claims (NNG_FromFnValues136.low claims) (NNG_FromFnValues136.high claims)) := by
  have selected := NNG_Array136.index claims 0#usize (by decide)
  unfold NNG_TreeSuffixes.f_a2
  rw [selected]
  exact blind fallback c env source s p prefixEq running terminal alpha claims t1 etaDom terminalDom alphaDom claimsDom
#print axioms row0

theorem high {W : Type} (fallback : Value) (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (running terminal : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript Unit)
    (etaDom : Domain s.challenges.eta) (terminalDom : Domain terminal) (alphaDom : DomainArray alpha) (claimsDom : DomainClaims claims) :
    All Checked (NNG_TreeSuffixes.f_a1 c s running terminal alpha t1 claims (NNG_FromFnValues136.low claims)) := by
  have selected : c.c0 10#usize (r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 s.digest) claims = .ok (NNG_FromFnValues136.high claims) := by
    rw [source.fromFn]
    exact NNG_FromFnValues136.second s.digest claims
  unfold NNG_TreeSuffixes.f_a1
  dsimp only
  rw [selected]
  exact row0 fallback c env source s p prefixEq running terminal alpha claims t1 etaDom terminalDom alphaDom claimsDom
#print axioms high

theorem low {W : Type} (fallback : Value) (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (running terminal : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript Unit)
    (etaDom : Domain s.challenges.eta) (terminalDom : Domain terminal) (alphaDom : DomainArray alpha) (claimsDom : DomainClaims claims) :
    All Checked (NNG_TreeSuffixes.f_a c s running terminal alpha t1 claims) := by
  have selected : c.c0 16#usize (r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 s.digest) claims = .ok (NNG_FromFnValues136.low claims) := by
    rw [source.fromFn]
    exact NNG_FromFnValues136.first s.digest claims
  unfold NNG_TreeSuffixes.f_a
  dsimp only
  rw [selected]
  exact high fallback c env source s p prefixEq running terminal alpha claims t1 etaDom terminalDom alphaDom claimsDom
#print axioms low

theorem mark3 {W : Type} (fallback : Value) (c : Calls) (env : RSL.Env) (source : NNG_SourceCalls136.Sources c env)
    (s : Parent Unit W) (p : LIB_VCarriers.Prefix) (prefixEq : s.prefixValue=NNG_LIBData.lowerPrefix p)
    (running terminal : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript Unit)
    (etaDom : Domain s.challenges.eta) (terminalDom : Domain terminal) (alphaDom : DomainArray alpha) (claimsDom : DomainClaims claims) :
    All Checked (NNG_TreeSuffixes.f_mark3 c s running terminal alpha t1 claims) := by
  unfold NNG_TreeSuffixes.f_mark3
  refine NNG_TraceAll136.bind Checked (NMT_CallTree.invoke "mark3" (s.observer,3#u8) (c.c9 s.observer 3#u8)) _ ?_ ?_
  · exact NNG_TraceAll136.invoke Checked _ _ _ (NNG_CheckedCalls136.mark3 _ _)
  · intro u returned
    cases u
    exact low fallback c env source s p prefixEq running terminal alpha claims t1 etaDom terminalDom alphaDom claimsDom
#print axioms mark3
end AspisR1.NNG_DomArrays136
