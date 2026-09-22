#include "model_cycles.hpp"
int main(){
 for(int seed : {1,2}) {
 auto h=build_h1(3,seed);auto g=build(3,"stride3",seed,true);
 int rh=rank(h),rg=rank(g);
 std::cout<<"{\"seed\":"<<seed<<",\"H1_rank\":"<<rh<<",\"G_rank\":"<<rg<<"}"<<std::endl;
 }
}
