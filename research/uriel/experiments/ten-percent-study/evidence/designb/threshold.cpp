// C++17. Exact relaxed threshold audit on a specified 32-residue dyadic labeling.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using Mask = uint16_t;
constexpr int full = 65535;

struct Branch {
    Mask leaves;
    int count;
    std::array<int,16> num{}, den{};
    std::array<Mask,16> forbidden{};
};

bool canonical(unsigned word,int stride,int residue) {
    return (word >> (stride-1+residue))&1;
}

std::vector<Branch> branches(unsigned word,int parity){
    std::vector<Branch> out;
    for(int m=0;m<=full;++m){
        Branch node{};
        node.leaves=m;
        node.count=__builtin_popcount(m);
        std::fill(node.den.begin(),node.den.end(),1);
        bool legal=true;
        for(int s=1;s<16 && legal;s*=2) for(int c=0;c<s && legal;++c){
            int sides[2]={};
            for(int i=c;i<16;i+=s) if(m & (1<<i)) sides[(i/s)%2]|=1<<i;
            bool ev=canonical(word,2*s,2*c+parity);
            if((sides[0]||sides[1])&&!sides[ev]){legal=false;break;}
            if(!sides[1-ev]) continue;
            int missing=0;
            for(int h=s;h<16;h+=2*s){
                bool pair=false;
                for(int i=c;i<16 && !pair;i+=s)
                    pair=(m & (1<<i)) && (m & (1<<((i+h)%16)));
                missing+=!pair;
            }
            for(int i=c;i<16;i+=s) if(sides[1-ev] & (1<<i)){
                node.num[i]+=2*missing; node.den[i]+=16/s;
            }
        }
        if(legal){
            for(int k=0;k<16;++k) for(int i=0;i<16;++i) if(m & (1<<i))
                node.forbidden[k] |= (1<<((i+k)%16)) | (1<<((i+31-k)%16));
            out.push_back(node);
        }
    }
    return out;
}

void audit(unsigned word,int A,int C){
    const bool root_even=canonical(word,1,0);
    auto first=branches(word,0), second=branches(word,1);
    int total=0, above=0, ties=0, best=-1000000, best_a=0,best_b=0, best_holes=0;
    std::array<int,16> p_holes{};
    for(const auto& a:first) for(const auto& b:second){
        if((root_even ? !b.count : !a.count) || a.count+b.count<14) continue;
        ++total;
        int holes=0;
        if(a.count+b.count<=16)
            for(auto excluded:a.forbidden) holes+=!(excluded&b.leaves);
        std::array<int,32> cs{};
        int used=0;
        for(int t=0;t<32;++t){
            const auto& v=(t%2) ? b : a;
            int i=t/2;
            if(!(v.leaves&(1<<i))) continue;
            int c=C*v.num[i]-A*v.den[i];
            if(bool(t%2)!=root_even) c+=2*C*holes-32*A;
            cs[used++]=c;
        }
        std::sort(cs.begin(), cs.begin()+used,std::greater<int>());
        int val=4*cs[13];
        for(int i=0;i<13;i++) val+=12*cs[i];
        if(val>best) {best=val;best_a=a.leaves;best_b=b.leaves;best_holes=holes;}
        if(val>0){++above;if(holes<16) ++p_holes[holes];}
        ties+=val==0;
    }
    std::cout<<word<<" "<<first.size()<<" "<<second.size()<<" "<<total<<" "<<above<<" "<<ties<<" "<<best<<" "<<best_a<<" "<<best_b<<" "<<best_holes<<" ";
    for(int i=0;i<16;i++) std::cout<<p_holes[i]<<" ";
    std::cout<<"\n";
}

int main(int argc,char** argv){
    if(argc<4) return 1;
    int A=std::atoi(argv[1]),C=std::atoi(argv[2]);
    for(int i=3;i<argc;i++) audit(std::strtoul(argv[i],nullptr,0),A,C);
}
