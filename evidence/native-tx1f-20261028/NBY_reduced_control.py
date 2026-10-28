import NBY_generate as g
g.text='use super::*;\n'+g.attrs+'''fn NBY_slot_last_sentinel_wrong(){let mut proof=[0u8;57607];proof[57606]=1;let nodes=slot(&proof,5);let byte=nodes[nodes.len()-1];assert!(!(byte==proof[57606]&&nodes.len()==32*SLOT_NODES[5]));}\n'''
g.cases=[('NBY_slot_last_sentinel_wrong',True)]
if __name__=='__main__':g.publish('NBY_reduced_control','candidate.rs',98)
