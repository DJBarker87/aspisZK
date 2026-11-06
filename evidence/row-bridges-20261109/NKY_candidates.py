from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'ledger20-20261109'
raw=lzma.decompress((P/'NKW_LEDGER.json.xz').read_bytes());baseline=json.loads(raw)
ids=['TX1:235','TX2:216','TX2:218'];rows=[r for r in baseline['rows']if r['row']in ids];assert len(rows)==3 and all(r['status']=='OPEN'for r in rows)
(E/'NKY_BASELINE_ROWS.json').write_text(json.dumps(rows,indent=1)+'\n')
roots={'TX1:235':'AspisR1.NKY_LevelsComplete.source','TX2:216':'AspisR1.NKY_BoxTotal.checkpoint','TX2:218':'AspisR1.NKY_BoxTotal.master'}
certs=[]
for row in rows:
 id=row['row'];box=id!='TX1:235'
 certs.append(dict(row=id,function=row['function'],status='CANDIDATE',local_gate='PENDING_FINAL_RAW_AUDIT',credit_waits_next_ledger_gate=True,lean_roots=[roots[id]],baseline_obligation_statement_hash=row['obligation_statement_hash'],baseline_frozen_body_sha256=row['frozen_body_sha256'],route='(y)/(ai)(5)/(ad)/(aq)/(aq)(5)/(au)/(aa)/(az)(2)',cohort_endpoint='Full native owned-carrier Result and total allocation/post/frame packet on SAME raw152/153 bytes; arbitrary Reservation, no returning witness on abort'if box else'Literal retained emitted-body port Result equals canonical representation of adopted NKI_LevelsCohort.model at SAME inputs for EVERY packet witness, plus LevelsFrame return/canonical frame',native_support=['NKY_K008','NKY_K009','NKY_K010','NKY_K015','NKY_K016','NKY_K017']if id=='TX2:216'else['NKY_K011','NKY_K012','NKY_K013','NKY_K018','NKY_K019','NKY_K020']if box else['NKI_K001','NKI_K002','NJL_K059','NJL_K060'],retained_trust='Existing Allocator/native-contract semantic transport/ABI/std/compiler/source-to-ELF; P6/D188 option A reclassification, not removal',hypothesis_inventory='NKY_HYPOTHESES.md',literal_port_review_required=not box))
(E/'NKY_CLOSED.json').write_text(json.dumps(dict(status='CANDIDATES_ONLY',baseline='evidence/ledger20-20261109/NKW_LEDGER.json.xz',baseline_sha256=hashlib.sha256(raw).hexdigest(),authoritative_delta=0,rows=certs),indent=1)+'\n')
(E/'NKY_LEDGER_DELTA.json').write_text(json.dumps(dict(basis='NKW_LEDGER',baseline_sha256=hashlib.sha256(raw).hexdigest(),applied=False,authoritative_delta=0,before={'CLOSED':560,'QUALIFIED':0,'OPEN':39,'TOTAL':599},proposed_after_next_gate={'CLOSED':563,'QUALIFIED':0,'OPEN':36,'TOTAL':599},candidate_rows=ids,new_count=3,gate='PENDING_FINAL_RAW_AUDIT_THEN_NEXT_LEDGER',all_original_edges_clauses_and_trust_rows_retained=True,no_other_status_change=True,baseline_rows='NKY_BASELINE_ROWS.json',hypothesis_inventory='NKY_HYPOTHESES.md'),indent=1)+'\n')
print('three candidate packets recorded; authoritative delta remains0')
