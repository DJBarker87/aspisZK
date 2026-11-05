fn NHU_expand_left_cut(weights:&mut [QM31;64],index:usize,parent:QM31,right:QM31){                weights[2 * index] = parent.sub(right);
}
