"""Explicit head-by-head congruence avoids whole-body tactic normalization."""
from pathlib import Path
E=Path(__file__).resolve().parent
p=E/'NMS_Effect242Fold.lean';s=p.read_text();s=s[:s.index(' unfold NMS_Effect242.validate')]
lines=[' unfold NMS_Effect242.validate']
def emit(depth,text):lines.append(' '*depth+text)
def bind(depth,name,law,rest):
 emit(depth,'apply NMS_RSLRefine.bind ('+law+')');emit(depth,'intro '+name);rest(depth)
def guard(depth,expression,rest):
 emit(depth,'cases hguard : '+expression+' with')
 emit(depth,'| false =>');rest(depth+2)
 emit(depth,'| true => exact refl _')
def flow(depth,name,rest):
 emit(depth,'cases '+name+' with')
 emit(depth,'| Break residual => exact refl _')
 emit(depth,'| Continue value =>');rest(depth+2)
def tryflow(depth,reply,rest):
 bind(depth,reply,'refl _',lambda d:flow(d,reply,rest))
# Each name `value` shadows only at an actually entered continuation. No
# theorem application contains an independently selected child reply.
def tail(d):
 bind(d,'reconstruction','children.reconstruct _ _ _',lambda d:
  tryflow(d,'flowStatement',lambda d:emit(d,'exact refl _')))
def scan(d):
 bind(d,'scanner','children.scan _',lambda d:tryflow(d,'flowScanner',tail))
def data(d):
 bind(d,'read','children.data _',lambda d:tryflow(d,'flowData',scan))
def first(d):
 bind(d,'firstAccount','children.first _',lambda d:
  bind(d,'accountReply','refl _',lambda d:tryflow(d,'flowAccount',data)))
def auth(d):
 bind(d,'authReply','child233 _ _ _ _ _',lambda d:tryflow(d,'flowAuth',first))
def slot(d):tryflow(d,'flowSlot',auth)
def lane(d):
 bind(d,'laneReply','children.lane _',lambda d:
  bind(d,'mappedLane','refl _',lambda d:tryflow(d,'flowLane',slot)))
def nullifier(d):bind(d,'nullifier','children.nullifier _',lane)
def pubkey(d):bind(d,'poolProgram','children.pubkey _',nullifier)
def poolcheck(d):bind(d,'poolMismatch','refl _',lambda d:guard(d,'poolMismatch',pubkey))
def pool(d):bind(d,'poolId','children.pool',poolcheck)
def release(d):bind(d,'releaseMismatch','refl _',lambda d:guard(d,'releaseMismatch',pool))
def profile(d):bind(d,'profileMismatch','refl _',lambda d:guard(d,'profileMismatch',release))
def decoder(d):
 bind(d,'decoded','children.decode _',lambda d:
  bind(d,'mappedDecode','refl _',lambda d:tryflow(d,'flowDecode',profile)))
bind(1,'requestSize','refl _',lambda d:guard(d,'(Slice.len data != requestSize)',decoder))
s+='\n'.join(lines)+'\n#print axioms fold\nend NMS_Effect242Fold\n'
p.write_text(s)
