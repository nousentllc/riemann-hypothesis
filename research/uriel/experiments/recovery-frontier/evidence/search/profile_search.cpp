// Exhaustive finite dyadic support/rate search. Compile with C++17.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
constexpr int n = 16;
using Row = array<int,n>;
using Bits = unsigned;
int pop(Bits x) { return __builtin_popcount(x); }
int bit(Bits x,int i) { return (x>>i)&1; }

struct Fraction {
    int top = 0, bottom = 1;
    bool smaller(const Fraction& other) const {
        return int64_t(top)*other.bottom < int64_t(other.top)*bottom;
    }
};
struct Best {
    Fraction f;
    Bits support = 0;
    Row rates{};
    void offer(int num,int den,Bits s,const Row& r) {
        if (den <= 0) abort();
        if (f.smaller({num,den})) {
            int g=gcd(num,den);
            f={num/g,den/g}; support=s; rates=r;
        }
    }
};

struct Node {int stride,base,width; Bits side[2];};
vector<Node> nodes;
int idx(int stride,int base) {return stride-1+base;}
void make_nodes() {
    for(int stride=1;stride<n;stride*=2)
        for(int base=0;base<stride;base++) {
            Node v{stride,base,n/stride,{0,0}};
            for(int j=0;j<v.width;j++)
                v.side[j%2] |= 1u << (base+j*stride);
            nodes.push_back(v);
        }
}

Bits transform(Bits ori,int u,int shift) {
    Bits result=0;
    for(int i=0;i<int(nodes.size());i++){
        auto v=nodes[i];
        int child=(v.base+v.stride*bit(ori,i))*u+shift;
        int base=child%v.stride;
        result |= ((child/v.stride)%2)<<idx(v.stride,base);
    }
    return result;
}
struct Orientation {
    Bits bits; int multiplicity; Row k{};
    Best uniform,uniform_pair, ternary,ternary_pair, relaxed;
};
vector<Orientation> representatives() {
    vector<bool> seen(1<<15); vector<Orientation> orientations;
    for(int i=0;i<(1<<15);i++) {
        if(seen[i]) continue;
        Orientation row{}; row.bits=i;
        for(int u=1;u<n;u+=2) for(int t=0;t<n;t++) {
            auto other=transform(i,u,t);
            if(!seen[other]) {seen[other]=true; row.multiplicity++;}
        }
        row.k.fill(1); // unresolved dyadic tail has mean 1/32 per unit
        for(int j=0;j<15;j++) for(int t=0;t<n;t++)
            if(bit(nodes[j].side[1-bit(i,j)],t)) row.k[t]+=nodes[j].width;
        orientations.push_back(row);
    }
    return orientations;
}
Row holes(Bits mask) {
    Row d{};
    for(int j=0;j<15;j++){
        auto v=nodes[j];
        for(int h=1;h<v.width;h+=2) {
            bool any=false;
            for(int i=0;i<v.width;i++) {
                int t=v.base+i*v.stride, end=v.base+(i+h)%v.width*v.stride;
                if(bit(mask,t)&&bit(mask,end)) {any=true;break;}
            }
            if(!any) d[j]++;
        }
    }
    return d;
}

struct Constraints {
    Bits required=0, value=0;
    bool possible=true;
    void choices(int j,bool allow0,bool allow1){
        if(!allow0 && !allow1) possible=false;
        if(allow0 != allow1) {
            required |= 1u<<j;
            if(allow1) value |= 1u<<j;
        }
    }
    bool allows(Bits ori) const {return possible && (ori&required)==value;}
};
// Python writes two rigorously certified tables of limiting cell success
// inequalities for rational rates, including the empty-cell and tile-product tests.
int single_table[17][33][33], pair_table[17][33][33];
struct Profile {
    Constraints single,pair;
    Row sums[2]{};
    int mass;
};
Profile evaluate_rates(const Row& rates,int denominator){
    Profile p{}; p.mass=accumulate(rates.begin(),rates.end(),0);
    for(int j=0;j<15;j++){
        int sums[2]={0,0};
        for(int t=0;t<n;t++) for(int b=0;b<2;b++)
            if(bit(nodes[j].side[b],t)) sums[b]+=rates[t];
        p.sums[0][j]=sums[0];p.sums[1][j]=sums[1];
        int width=nodes[j].width;
        // Equal-rate profiles store one mass unit per active leaf. The limiting
        // rate is 16/denominator, as opposed to integer ternary profiles.
        // Each table is selected by the main caller through a flattened key.
        int total=sums[0]+sums[1];
        auto passes=[&](int b,int criterion){
            if(!total) return true;
            // For homogeneous cases use the precomputed normalized table below.
            extern int hom_table[17][17][17][17][2];
            if(denominator) return bool(hom_table[denominator][width][total][sums[b]][criterion]);
            return bool((criterion?pair_table:single_table)[width][total][sums[b]]);
        };
        p.single.choices(j,passes(0,0),passes(1,0));
        p.pair.choices(j,passes(0,1),passes(1,1));
    }
    return p;
}
int hom_table[17][17][17][17][2];
void check_profile(const Row& rate,Bits mask,const Row& d,bool equal,vector<Orientation>& orientations){
    auto p=evaluate_rates(rate,equal?pop(mask):0);
    if(!p.pair.possible&&!p.single.possible) return;
    for(auto& o:orientations){
        bool pass1=p.single.allows(o.bits),pass2=p.pair.allows(o.bits);
        if(!pass1&&!pass2) continue;
        int den=p.mass,num=0;
        for(int j=0;j<15;j++){
            int odd=p.sums[1-bit(o.bits,j)][j];
            den+=nodes[j].width*odd;
            num+=2*d[j]*odd;
        }
        if(pass1) (equal?o.uniform:o.ternary).offer(num,den,mask,rate);
        if(pass2) (equal?o.uniform_pair:o.ternary_pair).offer(num,den,mask,rate);
    }
}
// Optimize over the closed box 0<=a_i<=23/10, total rate 16. Keep all
// supported-leaf geometry and relax the lower bounds on rates. Every proper
// vertex assigns the cap to 6 leaves and 22/10 to a seventh.
void relax(Bits mask,const Row& d,vector<Orientation>& orientations){
    Constraints necessary;
    for(int j=0;j<15;j++) {
        bool a=mask&nodes[j].side[0],b=mask&nodes[j].side[1];
        if(a||b) necessary.choices(j,a,b);
    }
    for(auto& o:orientations){
        if(!necessary.allows(o.bits)) continue;
        Row R{},order{};
        int m=0;
        for(int t=0;t<n;t++) if(bit(mask,t)){
            order[m++]=t;
            for(int j=0;j<15;j++) if(bit(nodes[j].side[1-bit(o.bits,j)],t)) R[t]+=2*d[j];
        }
        // A box vertex improves a trial quotient iff the linearized maximum is
        // positive; finite Dinkelbach iterations strictly improve a rational.
        Fraction cur=o.relaxed.f;
        for(;;){
            sort(order.begin(),order.begin()+m,[&](int a,int b){
                int64_t sa=int64_t(R[a])*cur.bottom-int64_t(o.k[a])*cur.top;
                int64_t sb=int64_t(R[b])*cur.bottom-int64_t(o.k[b])*cur.top;
                return sa!=sb?sa>sb:a<b;
            });
            int num=0,den=0; Row masses{};
            for(int i=0;i<7;i++){
                int t=order[i],z=(i==6?22:23);
                num+=z*R[t]; den+=z*o.k[t]; masses[t]=z;
            }
            if(!cur.smaller({num,den})) break;
            o.relaxed.offer(num,den,mask,masses); cur=o.relaxed.f;
        }
    }
}
void print_best(const Best& b){
    cout<<b.f.top<<" "<<b.f.bottom<<" "<<b.support<<" ";
    for(int i=0;i<n;i++)cout<<b.rates[i]<<(i+1==n?' ':',');
}
int main(){
    make_nodes(); auto orientations=representatives();
    // Dimensions are small; the Python generator verifies decisive exponential
    // comparisons using rational Taylor bounds before building these tables.
    int selector,w,a,b,p,q;
    while(cin>>selector>>w>>a>>b>>p>>q){
        if(selector==0){single_table[w][a][b]=p;pair_table[w][a][b]=q;}
        else {hom_table[selector][w][a][b][0]=p;hom_table[selector][w][a][b][1]=q;}
    }
    int support_count=0, ternary_count=0;
    for(Bits mask=1;mask<(1u<<n);mask++){
        int m=pop(mask); if(m<7)continue;
        Row d=holes(mask); bool productive=false;
        for(int j=0;j<15;j++) if(d[j]&&(mask&nodes[j].side[0])&&(mask&nodes[j].side[1])) productive=true;
        if(!productive)continue; // one-child supported nodes must put that child even.
        support_count++;
        Row rate{};
        for(int t=0;t<n;t++)rate[t]=bit(mask,t);
        check_profile(rate,mask,d,true,orientations); relax(mask,d,orientations);
        if(m<8)continue;
        int extra=16-m;
        for(Bits doubles=mask;;doubles=(doubles-1)&mask){
            if(pop(doubles)==extra){
                ternary_count++;
                for(int t=0;t<n;t++)rate[t]=bit(mask,t)+bit(doubles,t);
                check_profile(rate,mask,d,false,orientations);
            }
            if(!doubles)break;
        }
    }
    cout<<orientations.size()<<" "<<support_count<<" "<<ternary_count<<"\n";
    for(auto& o:orientations){
        cout<<o.bits<<" "<<o.multiplicity<<" ";
        for(auto b:{o.uniform,o.uniform_pair,o.ternary,o.ternary_pair,o.relaxed})print_best(b);
        cout<<"\n";
    }
}
