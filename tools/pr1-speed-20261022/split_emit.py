"""Split the independent emitter certificates, preserving their internal order."""
from pathlib import Path
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/z4/z9c.rs';s=p.read_text()
a=s.index('    // Lifts.\n',s.index('fn emit('));end=s.index('\n}\n',a)
old=s[a:end]
lift=old[old.index('    let mut tt = Instant::now();'):old.index('    info.t_lifts = tt.elapsed().as_secs_f64();')]
lift=lift.replace('let mut tt','let tt').replace('return (None, info);','return None;')
lift+='    info.t_lifts = tt.elapsed().as_secs_f64();\n    Some(lifts)\n'
q=old[old.index('    let targets ='):old.index('    // BCondG:')]
q=q.rsplit('    tt = Instant::now();',1)[0]
q=q.replace('return (None, info);','return None;')+'    Some((kept,qp_y))\n'
b=old[old.index('    // BCondG:'):old.index('    if p.qs.len() > 22')]
b=b.replace('return (None, info);','return None;')+'    Some((bc_u,bc_piv,bc_fr,gk,bc_y))\n'
new='''    // Cheap original first-lift rank gate before later certificate work.
    // The complete lift family still runs below, including this first lift.
    let w=lift_width(0);
    let mut first=TagEch::new(w);
    for m in lift_members(0) {
        if let Ins::Pivot=first.insert(lift_src(&p.cx,0,m)) {
            if first.rank()==w {break;}
        }
    }
    if first.rank()<w {
        info.lift_ranks.push(first.rank());info.fail=Some("lift rank below width");
        return (None,info);
    }
    enum Part { L(Option<Vec<Lift>>,EmitInfo), Q(Option<(Vec<LaneKer>,Vec<Vec<u32>>)>,EmitInfo), B(Option<(Vec<Vec<u32>>,Vec<u32>,Vec<u32>,LaneKer,Vec<Vec<u32>>)>,EmitInfo) }
    let mut parts = aspis_r1_cert_check::native_workers::ordered_families(3, |i| {
        let mut part_info=EmitInfo::default();
        match i {
            0 => {let x=emit_lifts(p,&mut part_info);Part::L(x,part_info)},
            1 => {let x=emit_qprime(p,&ln,&mut part_info);Part::Q(x,part_info)},
            _ => {let x=emit_bcond(p,&ln,&mut part_info);Part::B(x,part_info)},
        }
    }).into_iter();
    let Part::L(lifts,li)=parts.next().unwrap() else {unreachable!()};
    info.lift_ranks=li.lift_ranks;info.t_lifts=li.t_lifts;
    let Some(lifts)=lifts else {info.fail=li.fail;return (None,info)};
    let Part::Q(q,qi)=parts.next().unwrap() else {unreachable!()};
    info.rank_r=qi.rank_r;info.qp_entries=qi.qp_entries;info.qp_lanes_used=qi.qp_lanes_used;info.t_qprime=qi.t_qprime;
    let Some((kept,qp_y))=q else {info.fail=qi.fail;return (None,info)};
    let Part::B(b,bi)=parts.next().unwrap() else {unreachable!()};
    info.rel_rank=bi.rel_rank;info.g_piv=bi.g_piv;info.vg_rank=bi.vg_rank;info.t_bcond=bi.t_bcond;
    let Some((bc_u,bc_piv,bc_fr,gk,bc_y))=b else {info.fail=bi.fail;return (None,info)};
    if p.qs.len()>22 {info.fail=Some("QueryCard");return (None,info)}
    (Some(Cert { hinv, qp: kept, qp_y, bc_u, bc_piv, bc_fr, bc_g:gk, bc_y, lifts }),info)'''
s=s[:a]+new+s[end:]
funcs='\nfn emit_lifts(p:&Pub,info:&mut EmitInfo)->Option<Vec<Lift>> {\n'+lift+'}\n'
funcs+='fn emit_qprime(p:&Pub,ln:&Lanes,info:&mut EmitInfo)->Option<(Vec<LaneKer>,Vec<Vec<u32>>)> {\n    let a=&p.a; let tt=Instant::now();\n'+q+'}\n'
funcs+='fn emit_bcond(p:&Pub,ln:&Lanes,info:&mut EmitInfo)->Option<(Vec<Vec<u32>>,Vec<u32>,Vec<u32>,LaneKer,Vec<Vec<u32>>)> {\n    let tt=Instant::now();\n'+b+'}\n'
s+=funcs;p.write_text(s)
