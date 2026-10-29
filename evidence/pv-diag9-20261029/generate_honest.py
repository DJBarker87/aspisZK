exec((__import__('pathlib').Path(__file__).parent/'generate.py').read_text().split('import json')[0])
import subprocess,json
current='PV_DIAG9_Honest'
header='''open R1Z R1Z.PV_RunJoin_HonestIdentification26 PV_RunJoin_Outer30
local instance : BuilderForestAdmissionPort.ExternalLinear := R1Z.PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := R1Z.PV_RunJoin_UniversalRecords22.shipped
local instance : LaneRoot := R1Z.PV_RunJoin_LaneABI31.native
local notation "E" => R1Z.PV_RunJoin_ShippedExternal.E_shipped
local notation "R" => R1Z.PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
 [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
'''
steps=[('honest_compiler_no_panic','''/-- Complete Result, all modelled panic branches of this compiler invocation. -/
theorem honest_compiler_no_panic (i : Honest (K := K)) :
 @PV_Src_NativeInput.run E R (inputs i) ≠ .fail .panic :=
 ok_excludes_panic (PV_RunJoin_HonestIdentification26.success i)'''),
('honest_compiler_no_divergence','''theorem honest_compiler_no_divergence (i : Honest (K := K)) :
 @PV_Src_NativeInput.run E R (inputs i) ≠ .div :=
 ok_excludes_div (PV_RunJoin_HonestIdentification26.success i)'''),
('honest_compiler_no_outer_error','''theorem honest_compiler_no_outer_error (i : Honest (K := K)) (e : Error) :
 @PV_Src_NativeInput.run E R (inputs i) ≠ .fail e :=
 ok_excludes_failure (PV_RunJoin_HonestIdentification26.success i) e''')]
base='docs/research/v8-r0-zk-20261009/lean/R1Z/'
src=subprocess.check_output(['git','show','codex/pv-runjoin-20261026:'+base+'PV_RunJoin_CanonicalHonest31.lean'],text=True)
for kind in ['transfer','withdrawal']:
 start=src.index('theorem '+kind);stop=src.index(' := by',start);sig=src[start:stop]
 params,conclusion=sig.split(' :\n    ∃ root,',1)
 # Keep original honest-family conclusion and add its derived whole-compiler exclusion.
 params=params.replace('theorem '+kind,'theorem canonical_'+kind+'_no_panic')
 result=' :\n    ∃ root, '+conclusion+''' ∧
      @PV_Src_NativeInput.run E R
        (PV_RunJoin_OuterChecked30.'''+kind+'''Input p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c) ≠ .fail .panic := by
  obtain ⟨root,hr,hi⟩ := PV_RunJoin_CanonicalHonest31.'''+kind+''' (K := K) bytes p w context snapshot c h
  exact ⟨root,hr,hi,ok_excludes_panic hi.2.1⟩'''
 # HonestInput application must parenthesize prior to ∧; existing conclusion ends application) already fine.
 steps.append(('canonical_'+kind+'_no_panic',params+result))
steps.append(('same_public_not_needed_for_exclusion','''theorem same_public_not_needed_for_exclusion (i j : Honest (K := K)) :
 (@PV_Src_NativeInput.run E R (inputs i) ≠ .fail .panic) ∧
 (@PV_Src_NativeInput.run E R (inputs j) ≠ .fail .panic) :=
 ⟨honest_compiler_no_panic i,honest_compiler_no_panic j⟩'''))
module(current,['PV_DIAG9_Result','R1Z.PV_RunJoin_CanonicalHonest31','R1Z.PV_RunJoin_HonestIdentification26'],header,steps)
p=D/'plans.json';old=json.loads(p.read_text());old.update(modules);p.write_text(json.dumps(old,indent=2)+'\n')
(D/(current+'.lean')).write_text(modules[current][-1])
