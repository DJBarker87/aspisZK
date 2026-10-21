from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parent
original=(root/'source-original/Types.lean').read_text()
actual=(root/'sources/AspisR1CurrentCaller/Types.lean').read_text()
blocks={
'aspis_core.r0.Error':(['IndexOutOfRange','WrongLength','ZeroDenominator','Allocation','NonCanonical','WrongField','InvalidPoints','QuotientNotInImage','RankDeficient','Parse','Semantic','Schedule','Sampler','Commitment','Authentication','V1','V2'],{}),
'aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public':(['Transfer','Withdrawal'],{'Transfer':'_ _','Withdrawal':'_ _'}),
'verifier.Error':(['Parse','Semantic','Transcript','Relation','Merkle','Query','Checkpoint','Allocation'],{}),
'compact.CodecError':(['Length','NonZeroHigh','NonCanonical'],{}),
'transport.Variant':(['S1','S2','D'],{}),
'verifier.Phase':(['Parsed','Semantic','SemanticPart','Prepare','CheckpointRead','Merkle','Query','QueryPart','CheckpointWrite','Relation','Final'],{'SemanticPart':'_','Merkle':'_','Query':'_','QueryPart':'_ _'}),
'r1_wire.Error':(['Allocation','RowOrder','InvalidRow','Tag','Length','NonCanonical','Boundary','Terminal','EqualCirclePoints','TrailingBytes','Public'],{'RowOrder':'_ _','Tag':'_','Length':'_','NonCanonical':'_ _','Boundary':'_'})}
expected=original
for typ,(cases,payloads) in blocks.items():
 marker='inductive '+typ+' where'
 at=expected.index(marker)
 start=expected.rfind('@[discriminant',0,at)
 end=expected.index('\n\n',at)
 old=expected[start:end]
 attr=''
 if typ=='aspis_core.r0.Error': attr='@[rust_type "aspis_core::r0::Error"]\n'
 elif typ=='aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public': attr='@[rust_type\n  "aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public"]\n'
 body=old[old.index(marker):]
 newblock=attr+body+'\n'+'def '+typ+'.read_discriminant (x : '+typ+') : Isize :=\n  match x with\n'
 newblock+='\n'.join(f"  | .{c}{(' '+payloads[c]) if c in payloads else ''} => {i}#isize" for i,c in enumerate(cases))
 newblock+='\n\ninstance _root_.AspisR1CurrentCaller.'+typ+'.instDiscriminant :\n    Aeneas.Std.Discriminant '+typ+' Isize where\n  read_discriminant := '+typ+'.read_discriminant'
 expected=expected[:start]+newblock+expected[end:]
assert expected==actual, 'adapted Types differs outside exact seven discriminant replacements'
assert actual.count('@[discriminant isize')==0
sha=lambda b:hashlib.sha256(b).hexdigest()
report={'original_path':'/tmp/query-s4-caller-v4-parent-cut-20261021/sources/AspisR1CurrentCaller/Types.lean','original_sha256':sha(original.encode()),'adapted_path':'sources/AspisR1CurrentCaller/Types.lean','adapted_sha256':sha(actual.encode()),'discriminant_adapters':{typ:{'constructors':cases,'ordinals':list(range(len(cases))),'qualified_instance':'_root_.AspisR1CurrentCaller.'+typ+'.instDiscriminant'} for typ,(cases,payloads) in blocks.items()},'inverse_transform_check':'PASS'}
(root/'evidence/adapter-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
