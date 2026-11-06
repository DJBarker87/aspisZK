from pathlib import Path
import json,re
E=Path(__file__).resolve().parent;G=E/'NLV_generated';sites=json.loads((E/'NLV_SITES.json').read_text());s=(G/'NLV_Tree.lean').read_text()
s=s[:s.index('\ndef denote')]
s=s.replace('import NLV_Algebra','import NLV_RunLaws').replace('namespace AspisR1.NLV_Tree','namespace AspisR1.NLV_Emitted')
pos=s.index('\ndef suffix_returned')
s=s[:pos]+'''
def emittedTry {A : Type} (r : core.result.Result A verifier.Error) (k : A → Code Out) : Code Out := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | core.ops.control_flow.ControlFlow.Continue val => k val
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual
theorem try_run {A : Type} (h : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (r : core.result.Result A verifier.Error) (k : A → Code Out) (before : SdkC_Source.Log) :
 SdkC_Source.run h (emittedTry r k) before =
 match r with
 | .Err e => (ok (.Err e),before)
 | .Ok a => SdkC_Source.run h (k a) before := by
 cases r <;> rfl
#print axioms try_run
''' + s[pos:]
s=re.sub(r'   match r with\n   \| \.Err e => pure \(\.Err e\)\n   \| \.Ok (\w+) => (.*)',lambda m:'   emittedTry r (fun '+m[1]+' => '+m[2]+')',s)
s+='''
/-- Structural identity with the adopted emitted body, including every Try
residual and aborting pure step. No native cut is inferred. -/
theorem initial_source (cfg : Configuration) (i : Input) :
 suffix_guard cfg i = GExp_FirstCode.code cfg.base cfg.boundaries cfg.std
 i.hashv i.digest i.publicValue i.publicBytes i.proof i.k := by rfl
#print axioms initial_source
end AspisR1.NLV_Emitted
end
'''
(G/'NLV_Emitted.lean').write_text(s)
