// Extraction-only candidates. No native or cohort bridge credit is claimed.
const NDE_P:u64=2147483647;
fn sub_word_ref(x:u32,y:u32)->u32{((u64::from(x)+NDE_P-u64::from(y))%NDE_P)as u32}
fn sub_ref(x:Q,y:Q)->Q{Q{c0:C{a:sub_word_ref(x.c0.a,y.c0.a),b:sub_word_ref(x.c0.b,y.c0.b)},c1:C{a:sub_word_ref(x.c1.a,y.c1.a),b:sub_word_ref(x.c1.b,y.c1.b)}}}
fn cm_add_ref(x:C,y:C)->C{C{a:add_word_ref(x.a,y.a),b:add_word_ref(x.b,y.b)}}
fn cm_sub_ref(x:C,y:C)->C{C{a:sub_word_ref(x.a,y.a),b:sub_word_ref(x.b,y.b)}}
fn mul_word_ref(x:u32,y:u32)->u32{((u64::from(x)*u64::from(y))%NDE_P)as u32}
fn cm_mul_ref(x:C,y:C)->C{let ac=mul_word_ref(x.a,y.a);let bd=mul_word_ref(x.b,y.b);C{a:sub_word_ref(ac,bd),b:add_word_ref(mul_word_ref(x.a,y.b),mul_word_ref(x.b,y.a))}}
fn cm_r_ref(x:C)->C{C{a:sub_word_ref(add_word_ref(x.a,x.a),x.b),b:add_word_ref(x.a,add_word_ref(x.b,x.b))}}
fn mul_ref(x:Q,y:Q)->Q{let a=cm_mul_ref(x.c0,y.c0);let b=cm_mul_ref(x.c1,y.c1);Q{c0:cm_add_ref(a,cm_r_ref(b)),c1:cm_add_ref(cm_mul_ref(x.c0,y.c1),cm_mul_ref(x.c1,y.c0))}}
pub fn interpolation_limb_ref(w:[u32;3],c:[u32;3])->u32{reduce_ref(u64::from(w[0])*u64::from(c[0])+u64::from(w[1])*u64::from(c[1])+u64::from(w[2])*u64::from(c[2]))}
pub fn residual_ref(pv:[Q;2],pw:[Q;2],cv:[Q;2],cw:[Q;2],helper:Q,chi:Q)->Q{
 let d0=sub_ref(chi,pv[0]);let d1=sub_ref(chi,pv[1]);let d2=sub_ref(chi,cv[0]);let d3=sub_ref(chi,cv[1]);
 let pd=mul_ref(d0,d1);let cd=mul_ref(d2,d3);
 let pn=add_ref(mul_ref(pw[0],d1),mul_ref(pw[1],d0));let cn=add_ref(mul_ref(cw[0],d3),mul_ref(cw[1],d2));
 sub_ref(mul_ref(pd,add_ref(mul_ref(helper,cd),cn)),mul_ref(cd,pn))
}
fn equality_factor_ref(a:Q,b:Q)->Q{let ab=mul_ref(a,b);add_ref(add_ref(sub_ref(sub_ref(lift_ref(1),a),b),ab),ab)}
pub fn equality_ref(left:[Q;10],right:[Q;10])->Q{let mut product=equality_factor_ref(left[0],right[0]);let mut i=1usize;while i<10{product=mul_ref(product,equality_factor_ref(left[i],right[i]));i+=1;}product}
pub fn tag_step_ref(raw:[u64;4],v:Q,tag:u32)->[u64;4]{[raw[0]+u64::from(v.c0.a)*u64::from(tag),raw[1]+u64::from(v.c0.b)*u64::from(tag),raw[2]+u64::from(v.c1.a)*u64::from(tag),raw[3]+u64::from(v.c1.b)*u64::from(tag)]}
pub fn active_step_ref(sum:Q,high:Q,low:Q)->Q{add_ref(sum,mul_ref(high,low))}
pub fn pattern_step_ref(values:[Q;4],group:usize,pattern:Q,selector:Q)->[Q;4]{let mut out=values;out[group]=add_ref(out[group],mul_ref(pattern,selector));out}
pub fn fields_word_ref(value:u32)->Result<[u8;4],u8>{if value>=2147483647{Err(0)}else{Ok(value.to_le_bytes())}}
