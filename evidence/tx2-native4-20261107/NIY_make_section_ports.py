from NIY_port_tools import E,statement,head
import json
ns='NIY_SemanticPort';p,ctx,fa,ca,st=statement('NIY_ValidationCut','afterValidation');common=' '.join(n for n,t in ctx if n!='r34')
out=head(ns,['NIY_Z0xReadPort','NIY_C_SemanticCut','NIY_SectionBind'])+'\ntheorem source '+p+' :\n'+st+''' := by
 with_unfolding_all rw [NIY_SemanticCut.source,NIY_C_SemanticCut.source]
 unfold NIL_StatePort.reply NIL_FreshOps.semantic
 apply NIY_SectionBind.sectionReply
 rintro ⟨alpha,at1⟩
 have h := NIY_Z0xReadPort.source reserved d bytes v end1 i4 '''+common+''' (array unK alpha) {r34 with «at» := at1}
 simpa only [NIL_StatePort.reply,array_roundtrip unK k k_reverse,NIL_Carriers.reader] using h
#print axioms source
end '''+ns+'\n';(E/(ns+'.lean')).write_text(out)
ns='NIY_ValidationPort';p,ctx,fa,ca,st=statement('NIY_QueryCut','afterQueries')
out=head(ns,['NIY_SemanticPort','NIY_C_ValidationCut','NIY_SectionBind'])+'\ntheorem source '+p+' :\n'+st+''' := by
 with_unfolding_all rw [NIY_ValidationCut.source,NIY_C_ValidationCut.source]
 unfold NIL_StatePort.reply NIL_FreshOps.validate
 apply NIY_SectionBind.sectionReply
 intro unit
 have h := NIY_SemanticPort.source reserved d bytes v end1 i4 '''+fa+'''
 simpa only [NIL_StatePort.reply] using h
#print axioms source
end '''+ns+'\n';(E/(ns+'.lean')).write_text(out)
ns='NIY_QueryPort';p,ctx,fa,ca,st=statement('NIY_AfterRho','suffix');common=' '.join(n for n,t in ctx if n!='r12')
out=head(ns,['NIY_ValidationPort','NIY_C_QueryCut','NIY_QueryTransport'])+'\ntheorem source '+p+' :\n'+st+''' := by
 with_unfolding_all rw [NIY_QueryCut.source,NIY_C_QueryCut.source]
 unfold NIL_StatePort.reply
 apply NIY_QueryTransport.continuation
 intro queries out
 have h := NIY_ValidationPort.source reserved d bytes v end1 i4 '''+common+''' queries (unReader out)
 simpa only [NIL_StatePort.reply,reader_reverse] using h
#print axioms source
end '''+ns+'\n';(E/(ns+'.lean')).write_text(out)
print('Authored semantic, validation and ordered query ports at their literal source occurrences.')
