from pathlib import Path
import re
E=Path('evidence/lib-20261111')
s=Path('evidence/rowspec-lead-20261107/RSL_Verifier.lean').read_text().split('structure VLib where')[1].split('attribute [instance]')[0]
fields=re.findall(r'^  (\w+) :',s,re.M)
carriers=fields[:20]+['qDec','pDec']+fields[20:30]
mp={f:'LIB_VCarriers.'+f for f in carriers}
for names,ns in [('finishInputDom publicDom semanticRounds claims circle terminalQm31','LIB_VSemantic'),('semanticBytesDom parsePrefix publicTranscript','LIB_VParse'),('qadd qmul maskValue','LIB_VField'),('validatedRecord decodeK29 payload state','LIB_VRecordsAll'),('filled expandSemantic expandValues wideView','LIBC_VPrepare'),('parseShape canonicalScan accNew weightsNew finish','LIBC_VTx1A'),('batchMerkle geometry queryLoop checkpoint','LIBC_VTx1B')]:
 for f in names.split():mp[f]=ns+'.'+f
mp['begin']='LIB_VParse.begin_';mp['checkValuesDom']='LIBC_CheckValuesDomain.checkValuesDom'
# all remaining pure fields are actual carrier reads
for f in fields:mp.setdefault(f,'LIB_VCarriers.'+f)
imports='LIB_VField LIB_VRecordsAll LIB_VParse LIB_VSemantic LIBC_VPrepare LIBC_VTx1A LIBC_VTx1B LIBC_CheckValuesDomain'.split()
out=''.join('import '+x+'\n' for x in imports)+'set_option autoImplicit false\nnoncomputable section\nnamespace LIB_VLib\nopen RSL\n/-- The canonical TX1 library, assembled only from the merged concrete fields. -/\ndef library : VLib where\n'
for f in fields[:20]+['qDec','pDec']+fields[20:]:out+=f' {f} := {mp[f]}\n'
# projection equalities, each precisely fixes supplier graph/dom at SAME args
for f in fields+['qDec','pDec']:
 out+=f'theorem {f}_exact : library.{f} = {mp[f]} := rfl\n#print axioms {f}_exact\n'
entries=[('semanticRounds','LIB_VRounds','Prefix × Transcript','eval','a env'),('claims','LIB_VClaims','Prefix','eval','a env'),('terminalQm31','LIB_VTerminal','Public × Claims × Alpha × OrigChallenges','eval','a'),('circle','LIB_VCircle','Transcript × Record','eval','a env'),('parsePrefix','LIB_VParsePrefix','Bytes','eval','a'),('publicTranscript','LIB_VPublicTranscript','Public × B32','eval','a env'),('begin','LIB_VBegin','Prefix × Transcript','eval','a env')]
for f,ns,ty,ev,args in entries:
 out+=f'def {f}Value (a : {ty.replace("Public","LIB_VCarriers.Public").replace("Prefix","LIB_VCarriers.Prefix").replace("Transcript","LIB_VCarriers.Transcript").replace("OrigChallenges","LIB_VCarriers.OrigChallenges").replace("Claims","LIB_VCarriers.Claims").replace("Alpha","LIB_VCarriers.Alpha").replace("Record","LIB_VCarriers.Record")}) (env : Env) := {ns}.{ev} {args}\n'
 out+=f'theorem {f}_returns (a : {ty.replace("Public","LIB_VCarriers.Public").replace("Prefix","LIB_VCarriers.Prefix").replace("Transcript","LIB_VCarriers.Transcript").replace("OrigChallenges","LIB_VCarriers.OrigChallenges").replace("Claims","LIB_VCarriers.Claims").replace("Alpha","LIB_VCarriers.Alpha").replace("Record","LIB_VCarriers.Record")}) (env : Env) : NND_Returned.Returns (library.{f}.law a) env ({f}Value a env) := {ns}.returns a env\n#print axioms {f}_returns\n'
for f,ns,ty in [('filled','Filled','Nat'),('expandSemantic','ExpandSemantic','Bytes × Bytes'),('expandValues','ExpandValues','Bytes × Bytes'),('wideView','WideView','Bytes × Bytes × Bytes'),('parseShape','ParseShape','Bytes'),('canonicalScan','CanonicalScan','Bytes'),('accNew','AccNew','Unit'),('weightsNew','WeightsNew','LIB_VCarriers.Acc'),('finish','Finish','LIBC_Finish.Args'),('batchMerkle','BatchMerkle','LIBC_BatchMerkle.Args'),('geometry','Geometry','LIBC_Geometry.Args'),('queryLoop','QueryLoop','LIBC_QueryLoop.Args'),('checkpoint','Checkpoint','LIBC_Checkpoint.Args')]:
 args='env' if f=='accNew' else 'a env'
 out+=f'def {f}Value (a : {ty}) (env : Env) := LIBC_{ns}.value {args}\n'
 proof='by cases a; exact LIBC_AccNew.returns env' if f=='accNew' else f'LIBC_{ns}.returns a env'
 out+=f'theorem {f}_returns (a : {ty}) (env : Env) : NND_Returned.Returns (library.{f}.law a) env ({f}Value a env) := {proof}\n#print axioms {f}_returns\n'
out+='theorem reservation_functional : Child.Functional library.claims ∧ Child.Functional library.filled ∧ Child.Functional library.accNew ∧ Child.Functional library.weightsNew :=\n ⟨LIB_VClaims.functional,LIBC_Filled.functional,LIBC_AccNew.functional,LIBC_WeightsNew.functional⟩\n#print axioms reservation_functional\nend LIB_VLib\n'
(E/'LIB_VLib.lean').write_text(out)
