import NFS_ReadCanonical
import NFS_QueryInvariant
import OraclePortStdBuilder
import RPz7_FIp_Equality
import Port5Q1_GeometryAccessor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_CallerDomains
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody NFP_QueryCuts
open Port3_PushFrame (bind_success)

def select (seed : Ops) : Ops := {seed with
 op0:=@OraclePortStdBuilder.fromFn,op11:=Port4B_Opening.opening,
 op17:=FIp_CircleQuery.circle,op18:=Port5Q1_GeometryBinding.forQuery,
 op21:=NFS_ReadCanonical.read,widePartialEq:=FIp_Equality.dictionary}
def ops (seed : Ops) : Ops := NFS_QueryOps.installed (select seed)
/-- Every callable slot is selected concretely; no hidden callback law. -/
theorem no_seed (first second : Ops) : ops first=ops second := rfl

theorem loop_property {T F : Type} (dict : core.ops.function.FnMut F Usize T)
 (property : T → Prop)
 (call : ∀ state i value next,dict.call_mut state i=ok (value,next) → property value)
 (indices : List Usize) (state : F) (values : List T) (after : F)
 (run : OraclePortStdBuilder.fromFnLoop dict indices state=ok (values,after)) :
 ∀ x∈values,property x := by
 induction indices generalizing state values after with
 | nil => cases Result.ok.inj run; simp
 | cons i indices ih =>
  unfold OraclePortStdBuilder.fromFnLoop at run
  obtain ⟨⟨value,next⟩,hcall,run⟩ := bind_success _ _ _ run
  obtain ⟨⟨tail,last⟩,htail,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  intro x hx
  rcases List.mem_cons.mp hx with rfl|mem
  · exact call state i x next hcall
  · exact ih next tail after htail x mem

theorem array_property {T F : Type} (n : Usize) (dict : core.ops.function.FnMut F Usize T)
 (state : F) (out : Array T n) (property : T → Prop)
 (call : ∀ state i value next,dict.call_mut state i=ok (value,next) → property value)
 (run : OraclePortStdBuilder.fromFn n dict state=ok out) : ∀ x∈out.val,property x := by
 unfold OraclePortStdBuilder.fromFn at run
 obtain ⟨⟨values,after⟩,loop,run⟩ := bind_success _ _ _ run
 dsimp only at run
 split at run
 · have same := congrArg (fun a : Array T n=>a.val) (Result.ok.inj run)
   rw [←same]
   exact loop_property dict property call _ state values after loop
 · cases run

theorem fields (seed : Ops) (q : Slice U8) (values : Dots)
 (run : (ops seed).op0 4#usize
  (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (ops seed)) q=ok values) :
 ∀ x∈values.val,Port4C_QueryArithmetic.CanonE x := by
 apply array_property _ _ q values Port4C_QueryArithmetic.CanonE ?_ run
 intro state i value next call
 unfold verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut at call
 obtain ⟨bytes,hbytes,call⟩ := bind_success _ _ _ call
 obtain ⟨decoded,hdecoded,call⟩ := bind_success _ _ _ call
 cases Result.ok.inj call
 exact NFS_ReadCanonical.read_canonical bytes i value hdecoded

theorem dots (q : Slice U8) (g : Array E 29#usize) (qPlace gPlace : Nat)
 (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g)) (out : Dots)
 (run : FIp_DotsAdapter.dots q g=ok out) : ∀ x∈out.val,Port4C_QueryArithmetic.CanonE x := by
 have h := NFP_DotDomains.returned q g qPlace gPlace canonical out
  ((NFP_DotInstall.dot_result q g qPlace gPlace canonical).trans run)
 intro x member
 have c:=h x member
 exact ⟨⟨c.1.1.1,c.1.1.2,c.1.2.1,c.1.2.2⟩,⟨c.2.1.1,c.2.1.2,c.2.2.1,c.2.2.2⟩⟩

/-- One original query packet supplies both fold domains. No callee reply
success, canonical field reply or independent geometry is hypothesized. -/
theorem folds (seed : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize) (geometry : verifier.QueryGeometry)
 (u : Usize) (q : Slice U8) (d : Dots) (inverse : Array U32 5#usize)
 (circle : E) (values : Dots) (bad : Bool) (qPlace gPlace : Nat)
 (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g))
 (alpha0 : Port4C_QueryArithmetic.CanonE (p.alpha.val[0]'(by rw [p.alpha.property];decide)))
 (alpha1 : Port4C_QueryArithmetic.CanonE (p.alpha.val[1]'(by rw [p.alpha.property];decide)))
 (head : NFP_QueryCuts.head (ops seed) proof p a g=ok (u,q,d))
 (front : NFP_SuffixCuts.front (ops seed) p a geometry u q d=ok (inverse,circle,values,bad)) :
 NFS_NEI_CircleBridge.Domain (NFS_FoldInstall.raw (p.alpha.val[0]'(by rw [p.alpha.property];decide))) (NFS_FoldInstall.values d) ∧
 NFS_NEI_LineBridge.Domain (NFS_FoldInstall.raw (p.alpha.val[1]'(by rw [p.alpha.property];decide))) (NFS_FoldInstall.values values) := by
 obtain ⟨index,hindex,cast,opening,dot⟩ := NFP_HeadDomain.reached _ _ _ _ _ _ _ _ head
 have dc := dots q g qPlace gPlace canonical d dot
 unfold NFP_SuffixCuts.front at front
 iterate 15 obtain ⟨x,hx,front⟩ := bind_success _ _ _ front
 obtain ⟨iv,hi,front⟩ := bind_success _ _ _ front
 obtain ⟨alpha,ha,front⟩ := bind_success _ _ _ front
 obtain ⟨folded,hfold,front⟩ := bind_success _ _ _ front
 iterate 2 obtain ⟨x,hx,front⟩ := bind_success _ _ _ front
 obtain ⟨vs,hvalues,front⟩ := bind_success _ _ _ front
 iterate 3 obtain ⟨x,hx,front⟩ := bind_success _ _ _ front
 cases Result.ok.inj front
 exact ⟨(NFS_FoldInstall.domains _ d alpha0 dc).2,
  (NFS_FoldInstall.domains _ values alpha1 (fields seed q values hvalues)).1⟩
#print axioms no_seed
#print axioms loop_property
#print axioms array_property
#print axioms fields
#print axioms dots
#print axioms folds
end AspisR1.NFS_CallerDomains
end
