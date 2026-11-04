from pathlib import Path
E=Path(__file__).resolve().parent;p=E/'NFW_prepared_native_prepare.py';s=p.read_text()
s=s.replace('struct Ops {audit:bool,','struct Ops {payload_audit:bool,expected:[u8;6],audit:bool,')
s=s.replace('Ops{audit:false,','Ops{payload_audit:false,expected:[0;6],audit:false,')
s=s.replace('self.ops.calls+=1;self.ops.rows[i]=row;','''if self.ops.payload_audit&&i==target{let at=self.ops.positions[i];let value=if at<payload.len(){payload[at]}else{0};assert!((row==[27,28,29,30,31,32][i]&&payload.len()==[928,32,224,256,2048,0][i]&&value==self.ops.expected[i]&&(i>=4||self.ops.nonzero[i]==(i==0)))!=cfg!(NFW_invert));kani::assume(false);}self.ops.calls+=1;self.ops.rows[i]=row;''')
s=s.replace('let i=self.ops.sc;self.record(i,row,payload);self.ops.nonzero[i]=nonzero;', 'let i=self.ops.sc;self.ops.nonzero[i]=nonzero;self.record(i,row,payload);')
s=s.replace('o.audit=facet==16;','''o.audit=facet==16;o.payload_audit=facet==17;if facet==17{let mut ei=0;while ei<6{let at=o.positions[ei];o.expected[ei]=match ei{0=>if at<928{y1[at]}else{0},1=>if at<32{v.inactive.to_le_bytes()[at]}else{0},2=>if at<224{round0[at]}else{0},3=>if at<32{root[at]}else if at<256{round1[at-32]}else{0},4=>if at<2048{final_message[at]}else{0},_=>0};ei+=1;}}''')
s=s.replace('if facet==16{return;}','if facet==16||facet==17{return;}').replace('for j in range(17):','for j in range(18):')
p.write_text(s)
