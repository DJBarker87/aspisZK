from pathlib import Path
import re
L=Path(__file__).resolve().parents[2]/'lean'
s=(L/'FIs_Result.lean').read_text()
header=s[:s.index('def Outcome')].replace('namespace AspisR1.FIs_Result','namespace AspisR1.FJp_Result')
header='import FJp_ActualCaller\nimport FJp_RetSuffix\n'+header
defs=s[s.index('def Outcome'):s.index('theorem strengthen')].replace('FIs_Caller.Outcome','FJp_ActualCaller.Outcome')
th=s[s.index('theorem strengthen'):]
th=th.replace('theorem strengthen {W F CoreError : Type}','theorem strengthen {W C : Type} (err : C) (input : DrvC_Installation.Configuration FIo_Install.W C)\n    (r : NP6_StdModel.Reservation)')
a=th.index('    (adapterOps :');b=th.index('    (B :',a);th=th[:a]+th[b:]
cfg='(FIp_Install.configuration err input r)'
mp={'adapterOps':cfg+'.adapter','ops':cfg+'.currentBase','reserved':cfg+'.reserved','queryOps':cfg+'.query','geoOps':cfg+'.geometry','stageBase':cfg+'.stageBase','finishOps':cfg+'.finish','seed':'finishSeed'}
th=re.sub(r'\b('+ '|'.join(mp)+r')\b',lambda m:mp[m[0]],th)
th=th.replace('FinishOps F)','FinishOps FIo_Install.W)')
needle='    (old : FIs_P2P_Result.Outcome'
extras='''    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (⟨CFG.adapter,CFG.currentBase,CFG.stageBase,CFG.finish,CFG.reserved,
        CFG.query,CFG.geometry,F3M_CircleSource.install B,NP6_StdModel.calls reservation⟩ : DrvC_Installation.Configuration FIo_Install.W C)) native1 native2 hashv)
    (sha256 : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
'''.replace('CFG',cfg)
assert needle in th
th=th.replace(needle,extras+'    (old : FJp_Ret_Result.Outcome')
th=th.replace(',run,tx2,',',run,rootBinding,tx2,')
# The result deliberately drops the temporary root-retention fact.
th=th.replace('  refine ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,','  refine ⟨f,s,outer,pre,middle,fs,ss,run,tx2,')
start=th.index('    exact Or.inr ⟨accepted,nonrejecting,FIs_Caller.strengthen')
end=th.index('\n\n#print axioms',start)
call=th[start:end]
oldcall=call[call.index('FIs_Caller.strengthen'):]
assert oldcall.endswith('caller⟩')
oldcall=oldcall[:-1]
new='''    have original := '''+oldcall+'''
    exact Or.inr ⟨accepted,nonrejecting,FJp_ActualCaller.strengthen err input r L e1 e2 w1 w2
      B (NP6_StdModel.calls reservation) program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run prior tx2
      base.1 native1 native2 hashv extraction sha256 p1 syscall rootBinding original⟩'''
th=th[:start]+new+th[end:]
th=th.replace('end AspisR1.FIs_Result','end AspisR1.FJp_Result')
(L/'FJp_Result.lean').write_text(header+defs+th)
