// Audit all homogeneous size >=14 supports in Z/32 with a missing odd step.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <set>
#include <vector>
using Mask = uint32_t;
int pop(Mask x) {return __builtin_popcount(x);}
constexpr int Q=32;
struct Node {int s,c,w,bit; Mask child[2];};
std::vector<Node> tree;
void build_tree(){
    for(int s=1;s<Q;s*=2)for(int c=0;c<s;c++){
        Node n{s,c,Q/s,s-1+c,{0,0}};
        for(int t=c;t<Q;t+=s) n.child[(t/s)&1] |= 1u<<t;
        tree.push_back(n);
    }
}
std::set<Mask> candidates;
void independent(int pos,int n,int first,int previous, Mask mask){
    if(n+(Q-pos+1)/2<14) return;
    if(pos==Q){
        if(first&&previous) return;
        for(int h=1;h<16;h+=2){
            Mask image=0;
            for(int i=0;i<Q;i++) if((mask>>i)&1u) image|=1u<<((h*i)%Q);
            candidates.insert(image);
        }
        return;
    }
    independent(pos+1,n,first,0,mask);
    if(!previous) independent(pos+1,n+1,first||pos==0,1,mask|(1u<<pos));
}
using Pair=std::array<int,2>;
struct Profile{
    Mask mask; int k;
    int coarse_required,coarse_bits,bottom_required,bottom_bits;
    std::array<Pair,15> coeff;
    int base;
};
bool tile[17][33][17][17]{};
std::vector<Profile> profiles(int A,int C){
    std::vector<Profile> out;
    for(Mask mask:candidates){
        Profile p{};p.mask=mask;p.k=pop(mask);p.base=-A*p.k;
        if(!tile[p.k][2][2][1])continue;
        bool ok=true;
        for(auto node:tree){
            int a=pop(mask&node.child[0]),b=pop(mask&node.child[1]);
            if(!a&&!b) continue;
            bool pa=tile[p.k][node.w][a+b][a],pb=tile[p.k][node.w][a+b][b];
            if(!pa&&!pb){ok=false;break;}
            if(!pa||!pb){
                auto &req=node.s<16?p.coarse_required:p.bottom_required;
                auto &bits=node.s<16?p.coarse_bits:p.bottom_bits;
                int bit=node.s<16?node.bit:node.c;
                req|=1<<bit;
                if(pb) bits|=1<<bit;
            }
            int missing=0;
            Mask subset=mask&(node.child[0]|node.child[1]);
            for(int h=node.s;h<Q;h+=2*node.s){
                Mask shifted=(subset<<h)|(subset>>(Q-h));
                missing+=!(shifted&subset);
            }
            int unit=2*C*missing-A*node.w;
            if(node.s<16) p.coeff[node.bit]={b*unit,a*unit};
            else p.base+=unit*(a&&b);
        }
        if(ok)out.push_back(p);
    }
    return out;
}
int transform(int ori,int u,int shift){
    int result=0;
    for(auto n:tree) if(n.s<16){
        int child=(n.c+n.s*((ori>>n.bit)&1))*u+shift;
        int base=child%n.s;
        result|=((child/n.s)%2)<<(n.s-1+base);
    }
    return result;
}
int main(int argc,char**argv){
    int A=argc>1?std::atoi(argv[1]):1,C=argc>2?std::atoi(argv[2]):10;
    int k,w,n,a,ok;
    while(std::cin>>k>>w>>n>>a>>ok) tile[k][w][n][a]=ok;
    build_tree();independent(0,0,0,0,0);
    auto ps=profiles(A,C);
    std::array<bool,32768> seen{};
    int all=0,worst=0,none=0;
    std::cout<<"sets "<<candidates.size()<<" viable "<<ps.size()<<"\n";
    for(int word=0;word<32768;word++){
        if(seen[word])continue;
        for(int u=1;u<16;u+=2) for(int s=0;s<16;s++) seen[transform(word,u,s)]=true;
        std::array<bool,65536> covered{};int ncovered=0;
        int count=0;
        for(auto &p:ps){
            if((word&p.coarse_required)!=p.coarse_bits)continue;
            int diff=p.base;
            for(int i=0;i<15;i++)diff+=p.coeff[i][(word>>i)&1];
            if(diff<0) continue;
            ++count;
            int freebits=(~p.bottom_required)&65535;
            for(int lo=freebits;;lo=(lo-1)&freebits){
                int bot=p.bottom_bits|lo;
                if(!covered[bot]){covered[bot]=true;++ncovered;}
                if(!lo)break;
            }
            if(ncovered==65536)break;
        }
        int missed=65536-ncovered;
        all+=missed;worst=std::max(worst,missed);none+=(ncovered==0);
        int first=0;while(first<65536&&covered[first])first++;
        std::cout<<word<<" "<<ncovered<<" "<<count<<" "<<first<<"\n";
    }
    std::cout<<"missed "<<all<<" max "<<worst<<" none "<<none<<"\n";
}
