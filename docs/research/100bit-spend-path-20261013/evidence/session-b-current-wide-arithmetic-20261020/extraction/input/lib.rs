pub mod field;
pub fn wide_add(x:field::WideExact,y:field::WideExact)->field::WideExact{x.add(y)}
pub fn wide_sub(x:field::WideExact,y:field::WideExact)->field::WideExact{x.sub(y)}
pub fn wide_mul(x:field::WideExact,y:field::WideExact)->field::WideExact{x.mul(y)}
pub fn wide_scale(x:field::WideExact,y:field::M31)->field::WideExact{x.mul_m31(y)}
