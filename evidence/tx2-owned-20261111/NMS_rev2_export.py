"""Export and verify only after every disjoint own-root audit passed."""
from NMS_formal import *
if __name__=='__main__':
 a,mode=sys.argv[1:];assert mode in ['export','verify']
 r=run(a,'support','NMS_R2_'+mode,['python3','NMS_R2_retention.py',mode],{
  'NMS_R2_retention.py':(E/'NMS_R2_retention.py').read_text(),
  'NMS_R2_EXPORT_ENV.json':(E/'NMS_ENV.json').read_text(),
  'NMS_R2_AUDIT_ROOTS.json':(E/'NMS_R2_AUDIT_ROOTS.json').read_text()})
 sys.exit(r['exit_status'])
