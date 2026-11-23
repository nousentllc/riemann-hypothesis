// Exact closed-box upper bound for a fixed 64-leaf labeling. C++17, no libraries.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>

using Bits=uint32_t;
using Word=uint64_t;
using Int=int64_t;
constexpr int maximumSlots=26;
int pop(Bits x) { return __builtin_popcount(x); }
int preference(Word word,int stride,int base) { return (word>>(stride-1+base))&1; }
Bits rotate(Bits x,int k) { k&=31; return (x<<k)|(x>>((-k)&31)); }
Bits spread(Bits x) {
    x=(x|(x<<8))&0x00ff00ff; x=(x|(x<<4))&0x0f0f0f0f;
    x=(x|(x<<2))&0x33333333; return (x|(x<<1))&0x55555555;
}
Bits squeeze(Bits x) {
    x&=0x55555555; x=(x|(x>>1))&0x33333333; x=(x|(x>>2))&0x0f0f0f0f;
    x=(x|(x>>4))&0x00ff00ff; return (x|(x>>8))&0xffff;
}

struct MaskScore {
    int count=0;
    std::array<int,32> numerator{},denominator{};
    void append(const MaskScore& b,int gain=0,int cost=0) {
        for(int i=0;i<b.count;i++){
            numerator[count]=b.numerator[i]+gain;
            denominator[count++]=b.denominator[i]+cost;
        }
    }
};
struct Quarter {
    int base;
    Word word;
    std::vector<Bits> masks;
    std::array<int,65536> largest{};
    std::vector<std::vector<int>> inside;
    std::vector<MaskScore> coefficients;
    std::vector<std::array<Bits,16>> forbidden;
    Bits interior(Bits available,int c,int s) const {
        if(s==16) return available&(1u<<c);
        int child=preference(word,4*s,4*c+base);
        Bits even=interior(available,c+child*s,2*s);
        return even ? even|interior(available,c+(1-child)*s,2*s):0;
    }
    Quarter(Word label,int residue):base(residue),word(label) {
        std::vector<int> index(65536,-1);
        for(Bits m=0;m<65536;m++) if(interior(m,0,1)==m) {
            index[m]=masks.size(); masks.push_back(m);
        }
        for(Bits m=0;m<65536;m++) largest[m]=index[interior(m,0,1)];
        for(Bits m:masks) {
            std::vector<int> sub;
            for(int j=0;j<int(masks.size());j++) if(!(masks[j]&~m)) sub.push_back(j);
            std::sort(sub.begin(),sub.end(),[&](int i,int j){return pop(masks[i])>pop(masks[j]);});
            inside.push_back(std::move(sub));
            MaskScore values;
            for(int t=0;t<16;t++) if(m&(1u<<t)){
                int num=0,den=1;
                for(int s=1;s<16;s*=2){
                    int c=t%s;
                    if((t/s)%2==preference(word,4*s,4*c+base))continue;
                    den+=16/s;
                    for(int h=s;h<16;h+=2*s){
                        bool seen=false;
                        for(int y=c;y<16;y+=s)
                            if((m&(1u<<y))&&(m&(1u<<((y+h)%16)))) {seen=true;break;}
                        if(!seen)num+=2;
                    }
                }
                values.numerator[values.count]=num;values.denominator[values.count++]=den;
            }
            coefficients.push_back(values);
            std::array<Bits,16> f{};
            for(int k=0;k<16;k++)for(int t=0;t<16;t++)if(m&(1u<<t))
                f[k]|=(1u<<((t+k)%16))|(1u<<((t+31-k)%16));
            forbidden.push_back(f);
        }
        assert(masks.size()==1807);
    }
};

struct Value {
    int numerator=0,denominator=0;
    Word support=0;
    Int score=- (Int(1)<<59);
};
struct Threshold {
    int a,b;
    Int score(int n,int d)const{return Int(b)*n-Int(a)*d;}
};
using Table=std::array<std::array<Value,2>,maximumSlots+1>;
void consider(Value& best,Threshold z,int n,int d,Word support){
    Int v=z.score(n,d);
    if(v>best.score)best={n,d,support,v};
}
struct Unit {int n,d;Int score;};
std::array<Unit,64> ordered(const MaskScore& a,const MaskScore& b,Threshold z,int gain,int cost) {
    std::array<Unit,64> out;int m=0;
    for(int side=0;side<2;side++){
        const auto& v=side?b:a;
        for(int j=0;j<v.count;j++){
            int n=v.numerator[j]+side*gain,d=v.denominator[j]+side*cost;
            out[m++]={n,d,z.score(n,d)};
        }
    }
    std::sort(out.begin(),out.begin()+m,[](const Unit& x,const Unit& y){return x.score>y.score;});
    return out;
}
void profileTable(Table& table,const MaskScore& a,const MaskScore& b,Threshold z,
                  int gain,int cost,Word support){
    auto units=ordered(a,b,z,gain,cost);
    int n=0,d=0,count=a.count+b.count;
    for(int k=0;k<=std::min(maximumSlots,count);k++){
        consider(table[k][0],z,n,d,support);
        if(k==count)break;
        consider(table[k][1],z,n+8*units[k].n,d+8*units[k].d,support);
        n+=12*units[k].n;d+=12*units[k].d;
    }
}
Word embed(Word m,int base,int stride){
    Word out=0;
    for(;m;m&=m-1)out|=Word(1)<<(base+stride*__builtin_ctzll(m));
    return out;
}
Table combine(const Table& even,const Table& odd,Threshold z,int w){
    Table out{};
    for(int k=0;k<=maximumSlots;k++)for(int j=0;j<=maximumSlots-k;j++)
        for(int p=0;p<=1;p++)for(int q=0;q<=1-p;q++){
            const auto &a=even[k][p], &b=odd[j][q];
            if(a.score<-(Int(1)<<50)||b.score<-(Int(1)<<50))continue;
            consider(out[k+j][p+q],z,a.numerator+b.numerator,
                     a.denominator+b.denominator+w*(12*j+8*q),a.support|b.support);
        }
    return out;
}
Table quarterTable(const Quarter& q,Threshold z){
    Table t{};MaskScore empty;
    for(int i=0;i<int(q.masks.size());i++)
        profileTable(t,q.coefficients[i],empty,z,0,0,embed(q.masks[i],q.base,4));
    // With zero mass an otherwise required preferred minimum can carry zero in the closure.
    return t;
}
struct Side {
    int parity,ev;
    Quarter left,right;
    Side(Word word,int b):parity(b),ev(preference(word,2,b)),left(word,b),right(word,b+2){}
    int holes(int i,int j)const {
        if(pop(left.masks[i])+pop(right.masks[j])>16)return 0;
        int count=0;
        for(Bits ban:left.forbidden[i])count+=!(ban&right.masks[j]);
        return count;
    }
    MaskScore scores(int i,int j,int d) const {
        MaskScore s;
        s.append(left.coefficients[i],ev?2*d:0,ev?32:0);
        s.append(right.coefficients[j],ev?0:2*d,ev?0:32);
        return s;
    }
    Table envelope(Threshold z)const{
        Table u=quarterTable(left,z),v=quarterTable(right,z);
        Table t=ev?combine(v,u,z,32):combine(u,v,z,32);
        for(int i=0;i<int(left.masks.size());i++)for(int j=0;j<int(right.masks.size());j++){
            if(!(ev?right.masks[j]:left.masks[i])||!(ev?left.masks[i]:right.masks[j]))continue;
            int d=holes(i,j);
            if(!d)continue;
            const auto &x=left.coefficients[i], &y=right.coefficients[j];
            Word support=embed(left.masks[i],parity,4)|embed(right.masks[j],parity+2,4);
            profileTable(t,ev?y:x,ev?x:y,z,2*d,32,support);
        }
        return t;
    }
};
struct Audit {
    Word label;
    Side even,odd;
    Audit(Word word):label(word),even(word,preference(word,1,0)),odd(word,1-preference(word,1,0)){}
    Value bound(Threshold z,Word& raw,Word& unique,Value& noRoot){
        noRoot=combine(even.envelope(z),odd.envelope(z),z,64)[maximumSlots][1];
        Value best=noRoot;
        raw=0;unique=0;
        for(int l=0;l<int(even.left.masks.size());l++)for(int r=0;r<int(even.right.masks.size());r++){
            Bits m0=even.left.masks[l],m1=even.right.masks[r];
            if(!(even.ev?m1:m0))continue;
            Bits a=spread(m0)|(spread(m1)<<1);
            int nA=pop(a),need=std::max(1,maximumSlots+1-nA);
            if(nA>31)continue;
            std::array<Bits,16> forbidden{};
            bool cache=false;
            MaskScore leftScores;
            for(int j=0;j<16;j++){
                int k=even.parity==0?j:-j;
                forbidden[j]=rotate(a,k)|rotate(a,(even.parity==0?-1:1)-k);
            }
            for(int h=0;h<16;h++){
                Bits allowed=~forbidden[h];
                if(pop(allowed)<need)continue;
                int i=odd.left.largest[squeeze(allowed)],j=odd.right.largest[squeeze(allowed>>1)];
                Bits x=odd.left.masks[i],y=odd.right.masks[j];
                if(!(odd.ev?y:x)||pop(x)+pop(y)<need)continue;
                for(int bi:odd.left.inside[i]){
                    Bits b0=odd.left.masks[bi];
                    if(pop(b0)+pop(y)<need)break;
                    for(int bj:odd.right.inside[j]){
                        Bits b1=odd.right.masks[bj];if(pop(b0)+pop(b1)<need)break;
                        if(!(odd.ev?b1:b0))continue;
                        raw++;
                        Bits b=spread(b0)|(spread(b1)<<1);
                        int first=0;
                        for(;first<h;first++)if(!(forbidden[first]&b))break;
                        if(first<h)continue;
                        unique++;
                        if(!cache){leftScores=even.scores(l,r,even.holes(l,r));cache=true;}
                        int holes=0;for(Bits blocked:forbidden)holes+=2*!(blocked&b);
                        const auto rightScores=odd.scores(bi,bj,odd.holes(bi,bj));
                        const auto units=ordered(leftScores,rightScores,z,2*holes,64);
                        int n=8*units[maximumSlots].n,d=8*units[maximumSlots].d;
                        for(int s=0;s<maximumSlots;s++){n+=12*units[s].n;d+=12*units[s].d;}
                        if(z.score(n,d)>best.score)
                            consider(best,z,n,d,embed(a,even.parity,2)|embed(b,odd.parity,2));
                    }
                }
            }
        }
        return best;
    }
};
int main(int argc,char**argv){
    if(argc<2||argc>4)return 1;
    Word label=std::strtoull(argv[1],nullptr,0);
    if(label>>(63))return 2;
    Audit audit(label); Threshold z=argc==4? Threshold{std::atoi(argv[2]),std::atoi(argv[3])}:Threshold{1,7};
    if(z.a<0||z.b<=0)return 3;
    for(int iter=0;iter<12;iter++){
        Word raw,unique;Value noRoot;
        Value v=audit.bound(z,raw,unique,noRoot);
        std::cout<<label<<" "<<z.a<<" "<<z.b<<" "<<v.score<<" "<<v.numerator<<" "<<v.denominator
          <<" "<<v.support<<" "<<raw<<" "<<unique<<" "<<noRoot.numerator<<" "<<noRoot.denominator
          <<" "<<noRoot.support<<std::endl;
        if(argc==4||v.score==0)return 0;
        int g=std::gcd(v.numerator,v.denominator);z={v.numerator/g,v.denominator/g};
    }
    return 4;
}
