// Exact integer support oracle. Reuse the tested quarter support catalogs and masks.
#define main closed_box_program_main
#include "../upper/bound.cpp"
#undef main
#include <limits>
namespace priced {
Int base=100000;
int saturated=2393, partial=1782;  // Default mass unit 1/1000.
int minimumRootEven=1;
constexpr Int invalid=std::numeric_limits<Int>::min()/4;
struct Vertex {
    Int value=invalid;
    Word caps=0, rem=0;
};
struct Leaf { Int value; Word bit; };
using Layer=std::array<std::array<Vertex,2>,27>;
using Leaves=std::vector<Leaf>;
struct Query {
    int threshold;
    std::array<Int,64> prices;
    void keep(Vertex& best, Int value, Word caps, Word rem) const {
        if(value>best.value) best={value,caps,rem};
    }
    Leaves quarter(const Quarter& q,int i,int upstream) const {
        Leaves out;
        int j=0;
        for(Bits b=q.masks[i];b;b&=b-1) {
            const int t=4*__builtin_ctz(b)+q.base;
            const auto& c=q.coefficients[i];
            out.push_back({base*c.numerator[j]-Int(threshold)*(upstream+c.denominator[j])+prices[t],
                           Word(1)<<t});
            ++j;
        }
        return out;
    }
    Leaves joined(const Leaves& a,const Leaves& b,Int shiftA,Int shiftB) const {
        Leaves out;out.reserve(a.size()+b.size());
        for(auto l:a)out.push_back({l.value+shiftA,l.bit});
        for(auto l:b)out.push_back({l.value+shiftB,l.bit});
        return out;
    }
    void fill(Layer& t,Leaves v) const {
        std::sort(v.begin(),v.end(),[](Leaf a,Leaf b){return a.value>b.value;});
        Word caps=0;Int value=0;
        for(int j=0;j<=26 && j<=int(v.size());++j) {
            keep(t[j][0],value,caps,0);
            if(j==int(v.size())) break;
            keep(t[j][1],value+partial*v[j].value,caps,v[j].bit);
            value+=saturated*v[j].value;caps|=v[j].bit;
        }
    }
    Layer merge(const Layer& a,const Layer& b) const {
        Layer out{};
        for(int j=0;j<=26;++j)for(int k=0;j+k<=26;++k)
            for(int f=0;f<=1;++f)for(int g=0;f+g<=1;++g) {
                const auto l=a[j][f],r=b[k][g];
                if(l.value!=invalid && r.value!=invalid)
                    keep(out[j+k][f+g],l.value+r.value,l.caps|r.caps,l.rem|r.rem);
            }
        return out;
    }
    struct Half {
        std::vector<Leaves> a,b;
        Layer envelope;
    };
    Half prepare(const Side& side,int upstream) const {
        Half h; Layer left{},right{};
        for(int i=0;i<int(side.left.masks.size());++i) {
            h.a.push_back(quarter(side.left,i,upstream+32*side.ev));fill(left,h.a.back());
        }
        for(int j=0;j<int(side.right.masks.size());++j) {
            h.b.push_back(quarter(side.right,j,upstream+32*(1-side.ev)));fill(right,h.b.back());
        }
        h.envelope=merge(left,right);
        for(int i=1;i<int(h.a.size());++i)for(int j=1;j<int(h.b.size());++j){
            const int d=side.holes(i,j);
            if(d) fill(h.envelope,joined(h.a[i],h.b[j],2*base*d*side.ev,2*base*d*(1-side.ev)));
        }
        return h;
    }
    Leaves halfLeaves(const Side& s,const Half& h,int a,int b) const {
        const int d=s.holes(a,b);
        return joined(h.a[a],h.b[b],2*base*d*s.ev,2*base*d*(1-s.ev));
    }
    Vertex maximum(const Audit& groups) const {
        const auto& e=groups.even;const auto& o=groups.odd;
        const auto eh=prepare(e,0),oh=prepare(o,64);
        Vertex best=merge(eh.envelope,oh.envelope)[26][1];
        for(int l=0;l<int(e.left.masks.size());l++)for(int r=0;r<int(e.right.masks.size());r++){
            Bits m0=e.left.masks[l],m1=e.right.masks[r];
            if(!(e.ev?m1:m0))continue;
            Bits a=spread(m0)|(spread(m1)<<1);
            int nA=pop(a),need=std::max(1,27-nA);
            if(nA>31 || nA<minimumRootEven)continue;
            std::array<Bits,16> forbidden{};Leaves ev;bool cached=false;
            for(int j=0;j<16;j++){
                int k=e.parity==0?j:-j;
                forbidden[j]=rotate(a,k)|rotate(a,(e.parity==0?-1:1)-k);
            }
            for(int h=0;h<16;h++){
                Bits allowed=~forbidden[h];if(pop(allowed)<need)continue;
                int i=o.left.largest[squeeze(allowed)],j=o.right.largest[squeeze(allowed>>1)];
                Bits x=o.left.masks[i],y=o.right.masks[j];
                if(!(o.ev?y:x)||pop(x)+pop(y)<need)continue;
                for(int bi:o.left.inside[i]){
                    Bits b0=o.left.masks[bi];if(pop(b0)+pop(y)<need)break;
                    for(int bj:o.right.inside[j]){
                        Bits b1=o.right.masks[bj];if(pop(b0)+pop(b1)<need)break;
                        if(!(o.ev?b1:b0))continue;
                        Bits b=spread(b0)|(spread(b1)<<1);
                        int first=0;for(;first<h;first++)if(!(forbidden[first]&b))break;
                        if(first<h)continue;
                        if(!cached){ev=halfLeaves(e,eh,l,r);cached=true;}
                        int holes=0;for(Bits ban:forbidden)holes+=2*!(ban&b);
                        auto leaves=joined(ev,halfLeaves(o,oh,bi,bj),0,2*base*holes);
                        std::sort(leaves.begin(),leaves.end(),[](Leaf x,Leaf y){return x.value>y.value;});
                        Int v=partial*leaves[26].value;Word caps=0;
                        for(int k=0;k<26;k++){v+=saturated*leaves[k].value;caps|=leaves[k].bit;}
                        keep(best,v,caps,leaves[26].bit);
                    }
                }
            }
        }
        return best;
    }
};
}
int main(int argc,char**argv) {
    using namespace priced;
    if(argc!=2 && argc!=5 && argc!=6)return 1;
    if(argc>=5){
        base=std::stoll(argv[2]);
        saturated=std::stoi(argv[3]);
        partial=64*std::stoi(argv[4])-26*saturated;
        if(base<=0 || partial<=0 || partial>=saturated)return 1;
    }
    if(argc==6)minimumRootEven=std::stoi(argv[5]);
    Word w=std::stoull(argv[1]);if(w>>63)return 2;
    Audit groups(w);
    priced::Query q{};
    while(std::cin>>q.threshold) {
        for(auto& p:q.prices)if(!(std::cin>>p))return 3;
        auto v=q.maximum(groups);
        std::cout<<v.value<<" "<<v.caps<<" "<<v.rem<<std::endl;
    }
}
