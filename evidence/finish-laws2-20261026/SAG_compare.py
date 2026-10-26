"""Recheck statement correspondence from retained successful kernel output."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent
s=(P/'SAG_084/stdout.log').read_text()
a=s.split('@AspisR1.SAF_Deployed.deployed : ',1)[1].split('@AspisR1.SAG_SharedDeployed.deployed : ',1)[0].strip()
b=s.split('@AspisR1.SAG_SharedDeployed.deployed : ',1)[1].split('@AspisR1.SAG_Deployed.deployed : ',1)[0].strip()
c=s.split('@AspisR1.SAG_Deployed.deployed : ',1)[1].split("'AspisR1.SAG_Deployed.deployed' depends",1)[0].strip()
new=(P/'SAG_085/stdout.log').read_text().split(':=\n',1)[1].split('=>\n',1)[1].strip()
def normalize(x):
    return re.sub(r'\s+','',x.replace('AspisR1.SAG_ScaleConfig.configuration','AspisR1.Rc3_Install.configuration')
        .replace('AspisR1.SAF_C_SAF_FinalResult.Outcome','RESULT')
        .replace('AspisR1.SAG_FinalResult.Outcome','RESULT').replace('AspisR1.SAG_Q_Result.Outcome','RESULT'))
old_header,old_conclusion=a.split('AspisR1.DrvC_Implementation.driver',1)
old_conclusion='AspisR1.DrvC_Implementation.driver'+old_conclusion
new_header=c.split('AspisR1.SAG_SourceStatement.Conclusion',1)[0]
checks={'shared_generic_outer_and_conclusion_names_only':normalize(a)==normalize(b),
    'new_outer_only_explicit_source_index_change':normalize(old_header)==normalize(new_header),
    'new_conclusion_only_explicit_source_index_and_result_name_changes':normalize(old_conclusion)==normalize(new)}
assert all(checks.values()),checks
files=['SAG_084/stdout.log','SAG_085/stdout.log','SAG_090/stdout.log','SAG_091/stdout.log']
out={'checks':checks,'method':'Normalize pretty-printer whitespace; rename source configuration and result only. Text correspondence, not a new Lean equality theorem; arithmetic field discharge separately kernel checked.',
    'scope_warning':'Native scalar specialization is explicit; exact old dictionary requires SAG_ScaleScope.compatible conditions.',
    'new_outer_expands':'SAG_ScaleConfig.configuration c reservation = Rc3_Install.configuration (SAG_ScaleConfig.select c) reservation',
    'axioms':'standard only; SAG_078/SAG_084',
    'evidence':{f:hashlib.sha256((P/f).read_bytes()).hexdigest() for f in files}}
(P/'SAG_statement_comparison.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(checks))
