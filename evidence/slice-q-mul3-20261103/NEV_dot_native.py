"""Strict local-cut evidence; OPEN caller until all missing edges close."""
from NEV_dot_aux import *
def run():
 auxiliary=__import__('NEV_dot_aux').run()
 pairs=[pair('NEV_K058','NEV_K059','dots_term_cell','NEV_wrong_dots_term'),pair('NEV_K060','NEV_K061','dots_fold_cell','NEV_wrong_dots_fold'),pair('NEV_K066','NEV_K067','dots_tail_window','NEV_wrong_dots_tail_window')]
 controls=[copies('NEV_K063','NEV_K064',['NEV_K058','NEV_K059','NEV_K060','NEV_K061']),copies('NEV_K068','NEV_K069',['NEV_K066','NEV_K067'])]
 excluded=[]
 for label in ['NEV_K062','NEV_K065']:
  receipt=obj(E/label/'receipt.json');log=(E/label/'stdout.log').read_text()
  assert receipt['exit_status']!=0 and 'CBMC timed out' in log
  excluded.append(dict(attempt=label,reason='TIMEOUT: no credit, never rerun unchanged',wall_seconds=receipt['wall_seconds'],rss_kib=receipt['peak_rss_kib']))
 preflight=own_native('NEV_K070',0,'fast_pairing::canonical::NEV_dot_ctor::dots_outer_cursor')
 return dict(status='OPEN_CALLER',closed_rows=[],auxiliary=auxiliary,native_pairs=pairs,copy_controls=controls,excluded=excluded,unpaired_preflight=dict(attempt='NEV_K070',status='NO_CREDIT_MISSING_MATCHED_CONTROL'),budget=dict(kani_labels_used=70,kani_limit=70),remaining=['SAME immutable g selected-coefficient native window association','Complete StepBy specialized prestate/state association and matched control','Complete main-loop invariant/step association and callee domain propagation','four_dots native fixed-call/borrow/output context','Incoming caller certificates; both roots OPEN'])
if __name__=='__main__':
 result=run();(E/'NEV_DOT_NATIVE_REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'])
