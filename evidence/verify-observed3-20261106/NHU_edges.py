from pathlib import Path
import json
E=Path(__file__).resolve().parent
entries=[
 ('TX1:076','TX1:074','SAME c1/mask coefficient input canonical; coordinate=column%4<4','NHU_Mask.result; NHU_MaskHelpers.coordinate; retained coefficient-step/body-loop models','K016/017;K018/019'),
 ('TX1:076','TX1:073','SAME explicit linear returned from SAME point10; canonical linear from NHU_Linears.result','NHU_Power.domains; NHU_Mask.result; retained selected-mask caller model','K022/023;K024/025'),
 ('TX1:076','TX1:075','SAME borrowed canonical point10, exact two returned linears; no replacement point','NHU_Linears.loop/result; NHU_Mask.result/adopted','K024/025'),
 ('TX1:073','TX1:032','SAME canonical receiver and each of four SAME canonical square intermediates','NHU_Power.source/result/domains; imported NGH square packet','K010/011'),
 ('TX1:073','TX1:029','SAME two canonical multiplication operand pairs in exact six-call sequence','NHU_Power.domains; retained total product/probe laws','K010/011'),
 ('TX1:230','TX1:039','SAME four canonical lanes including actual zero padding from SAME values[N]; N2/12/16/17; bounds start+N<=96','NHU_Preweighted.result; NHU_PreweightedDomains; retained group/pack/loop induction','K045/046;K047/048;K049/050;K051/052'),
 ('TX1:248','TX1:262','SAME selectors owner, canonical high; exact singleton range0..57 within64; canonical low is the native packet domain','NHU_PoseidonSelectors.bounds/source/result; NHG_ExtraLeaves.sum_result','K055/056'),
 ('TX1:326','TX1:032','SAME canonical receiver and first square; zero allowed','NHU_Pow5.source/result/domains; imported NGH square packet','K060/061'),
 ('TX1:326','TX1:029','SAME canonical fourth power and original receiver','NHU_Pow5.domains; retained total product/probe laws','K060/061'),
 ('TX1:322','TX1:020','SAME six canonical U32s; each natural widened product<=P2; sum<=3*P2<2^64; reducer accepts every U64','NHU_U64Product.result; NHU_InterpolationRaw.result; NHU_Interpolation.source/result; retained current_wrapper_mod','K068/069')]
rows=[dict(caller=a,callee=b,domain=c,model_domain_proof=d,native=e,status='CLOSED internal domain association; no enclosing caller credit') for a,b,c,d,e in entries]
(E/'NHU_EDGES.json').write_text(json.dumps(dict(inherited='evidence/verify-observed2-20261106/NHG_EDGES.json',closed_edges=rows,finish136_closed=False,root137_closed=False,prepare_op9_instantiated=False,notes='Only listed internal edges of CLOSED NHU units. No edge from OPEN finish/root/prepare is closed.'),indent=1)+'\n')
