from pathlib import Path
L=Path(__file__).resolve().parents[2]/'lean'
items=[('Literal','FIs_Literal','FJp_NativeLiteral',[],'''  obtain ⟨raw,parsed,q,metadata,view,physical,stored,parser,queries,found,read,opened,
    fields,numeric,prepare,prepared,out,output,sourceNumeric,remaining⟩ := new
  refine ⟨raw,parsed,q,metadata,view,physical,stored,parser,queries,found,read,opened,
    fields,numeric,prepare,prepared,out,output,sourceNumeric,?_⟩
  rcases remaining with hit | good
  · exact Or.inl hit
  · right
    obtain ⟨acc,writer,len,next,savedEq,finishing⟩ := good
    exact ⟨acc,writer,len,next,savedEq,FJp_Finish.forget (new := finishing)⟩
'''),('Cont','FIs_Cont','FJp_ActualCont',['FJp_LiteralForget'],'''  obtain ⟨parsed,frame,parser,read,target,literal⟩ := new
  exact ⟨parsed,frame,parser,read,target,FJp_LiteralForget.value (new := literal)⟩
'''),('Caller','FIs_Caller','FJp_ActualCaller',['FJp_ContForget'],'''  obtain ⟨parsed,facts,sites,cont⟩ := new
  exact ⟨parsed,facts,sites,FJp_ContForget.value (new := cont)⟩
'''),('Result','FIs_Result','FJp_Result',['FJp_CallerForget'],'''  obtain ⟨f,s,outer,pre,middle,fs,ss,run,tx2,origin,calls,encoding,base,initial,selected,publicFacts,parser,
    version,writerKey,readerKey,physical,persistent,packet,safe,whole,branch⟩ := new
  refine ⟨f,s,outer,pre,middle,fs,ss,run,tx2,origin,calls,encoding,base,initial,selected,publicFacts,parser,
    version,writerKey,readerKey,physical,persistent,packet,safe,whole,?_⟩
  rcases branch with hit | good
  · exact Or.inl hit
  · exact Or.inr ⟨good.1,good.2.1,FJp_CallerForget.value (new := good.2.2)⟩
''')]
args={
'Literal':'adapter ops reserved query geo stage finish B std saved f s run H trace authParsed tx2',
'Cont':'adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd prior H f s saved run tx2',
'Caller':'L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run prior tx2',
'Result':'L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B reservation program data1 data2 slot saved post1 post2 H driver prior events hashv bad'}
for label,old,new,imports,body in items:
 src=(L/(old+'.lean')).read_text();head=src[:src.index('def Outcome')];head=head[head.index('set_option autoImplicit false'):]
 head=head.replace('namespace AspisR1.'+old,'namespace AspisR1.FJp_'+label+'Forget')
 sig=src[src.index('def Outcome'):src.index(' : Prop :=',src.index('def Outcome'))].replace('def Outcome','theorem value',1)
 a=args[label]
 out=''.join('import '+n+'\n' for n in [old,new]+imports)+head+sig+'\n    (new : '+new+'.Outcome '+a+') :\n    '+old+'.Outcome '+a+' := by\n'+body+'#print axioms value\nend AspisR1.FJp_'+label+'Forget\nend\n'
 (L/('FJp_'+label+'Forget.lean')).write_text(out)
