from pathlib import Path
L=Path(__file__).resolve().parents[2]/'docs/research/v8-r0-zk-20261009/lean/R1Z'
for name in ['Unread','Prefix']:
 s=(L/f'PV_OWNB_Sink{name}.lean').read_text()
 s=s.replace('import R1Z.PV_OWNB_Cursor','import R1Z.PV_OWNB_ActualSink')
 s=s.replace(f'PV_OWNB_Sink{name}',f'PV_OWNB_ActualSink{name}')
 s=s.replace('(v : PV_OWN_Link.Link)', '(v : PV_OWN_Link.Link) (actual : PV_OWN_Bytes.Bytes)')
 s=s.replace('sink q v','PV_OWNB_ActualSink.sink q v actual').replace('unfold sink NativeView','unfold PV_OWNB_ActualSink.sink NativeView')
 (L/f'PV_OWNB_ActualSink{name}.lean').write_text(s)
s=(L/'PV_OWNB_SinkValid.lean').read_text()
s=s.replace('PV_OWNB_SinkOwnership','PV_OWNB_ActualSink').replace('PV_OWNB_SinkNew','PV_OWNB_ActualSinkNew').replace('PV_OWNB_SinkUnread','PV_OWNB_ActualSinkUnread').replace('PV_OWNB_SinkPrefix','PV_OWNB_ActualSinkPrefix').replace('PV_OWNB_SinkValid','PV_OWNB_ActualSinkValid')
s=s.replace('(v : PV_OWN_Link.Link)', '(v : PV_OWN_Link.Link) (actual : PV_OWN_Bytes.Bytes)')
s=s.replace('(room:q.written<q.read)', '(room:q.written<q.read) (bytes:PV_OWNB_Padding.Agrees (PV_OWNB_LinkBytes.encode v) actual)')
s=s.replace('sink q v', 'PV_OWNB_ActualSink.sink q v actual').replace('PV_OWNB_ActualSink.owned q v h','PV_OWNB_ActualSink.ownership q v actual h').replace('initialized q v h room','initialized q v actual h room bytes').replace('frame q v h','frame q v actual h').replace('[sink,','[PV_OWNB_ActualSink.sink,').replace('[sink]','[PV_OWNB_ActualSink.sink]')
(L/'PV_OWNB_ActualSinkValid.lean').write_text(s)
