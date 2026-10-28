import NBY_generate as g
for i,c in [(0,0),(21,831)]:
 g.pair(f'opening_boundary_{i}_{c}',f'''let proof:[u8;57607]=kani::any();let q=opening(&proof,{i});let byte=q[{c}];''',f'byte==proof[10055+832*{i}+{c}]&&q.len()==832')
for s in [0,5]:
 coordinate='0' if s==0 else 'nodes.len()-1'
 offset='compact::slot_offset(0)' if s==0 else 'compact::slot_offset(6)-1'
 g.pair(f'slot_boundary_{s}',f'''let proof:[u8;57607]=kani::any();let nodes=slot(&proof,{s});let byte=nodes[{coordinate}];''',f'byte==proof[{offset}]&&nodes.len()==32*SLOT_NODES[{s}]')
if __name__=='__main__':g.publish('NBY_boundary','candidate.rs',73)
