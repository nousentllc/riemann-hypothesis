// Independent census: Horn-closure branching on root cycles and literal half-mask optimization.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using U=uint32_t;using W=uint64_t;using I=int64_t;
int size(W x){return __builtin_popcountll(x);}
int next(W x){return __builtin_ctzll(x);}
struct Check{
    W label;int a,b;
    W required[64]{},dependent[64]{};
    struct Node {W members,odd;int stride,width;};
    std::vector<Node> nodes;
    int denominator[64]{};
    W assigned=0,visits=0,claims=0;
    I rooted=-(I(1)<<55);
    W bestMask=0;
    Check(W word,int top,int bottom):label(word),a(top),b(bottom) {
        for(int s=1;s<64;s*=2)for(int c=0;c<s;c++){
            int child=(label>>(s-1+c))&1, pos=c+child*s;
            for(int t=2*s;t<64;t*=2)pos+=((label>>(t-1+pos))&1)*t;
            Node n{0,0,s,64/s};
            for(int j=c;j<64;j+=s){
                required[j]|=W(1)<<pos;n.members|=W(1)<<j;
                if((j/s)%2!=child){n.odd|=W(1)<<j;denominator[j]+=n.width;}
            }
            nodes.push_back(n);
        }
        for(int i=0;i<64;i++){required[i]|=W(1)<<i;denominator[i]++;
            for(W q=required[i];q;q&=q-1)dependent[next(q)]|=W(1)<<i;}
    }
    static W rotate(W x,int s){return (x<<s)|(x>>(64-s));}
    std::vector<int> sortedScores(W m,bool root)const{
        int ns[64]={};
        for(const auto &v:nodes){
            W odd=m&v.odd;
            if(!odd||v.width==2||(!root&&v.width==64))continue;
            W f=m&v.members;if(size(f)>v.width/2)continue;
            int d=0;for(int h=v.stride;h<64;h+=2*v.stride)d+=!(f&rotate(f,h));
            for(;odd;odd&=odd-1)ns[next(odd)]+=2*d;
        }
        std::vector<int> scores;
        for(W q=m;q;q&=q-1){int t=next(q);scores.push_back(b*ns[t]-a*denominator[t]);}
        std::sort(scores.begin(),scores.end(),std::greater<int>());return scores;
    }
    void branch(int h,W must,W ban){
        if(size(~ban)<27)return;
        W candidates=~(must|ban);
        if(!candidates){
            if(!(nodes[0].odd&must))return; // zero odd mass already belongs to the base envelope
            claims++;
            for(int j=1;j<h;j+=2)if(!(must&rotate(must,j)))return;
            visits++;
            auto sc=sortedScores(must,true);
            I value=8*sc[26];for(int k=0;k<26;k++)value+=12*sc[k];
            if(value>rooted){rooted=value;bestMask=must;}
            return;
        }
        int t=next(candidates);
        branch(h,must,ban|dependent[t]);
        W added=required[t]&~must;
        if(added&ban)return;
        W m=must|added;
        W neighbors=rotate(added,h)|rotate(added,64-h);
        if(m&neighbors)return;
        for(W q=neighbors;q;q&=q-1)ban|=dependent[next(q)];
        if(!(m&ban))branch(h,m,ban);
    }
    std::vector<W> valid(int c,int s)const{
        if(s==64)return {0,W(1)<<c};
        int choice=(label>>(s-1+c))&1;
        auto e=valid(c+choice*s,s*2),o=valid(c+(1-choice)*s,s*2);
        std::vector<W> out{0};out.reserve(1+(e.size()-1)*o.size());
        for(W i:e)if(i)for(W j:o)out.push_back(i|j);return out;
    }
    using Env=std::array<std::array<I,2>,27>;
    Env half(int side)const{
        Env tab;for(auto &r:tab)r.fill(-(I(1)<<52));
        auto masks=valid(side,2);assert(masks.size()==3263443);
        for(W m:masks){
            auto sc=sortedScores(m,false);I sum=0;
            for(int k=0;k<=26&&k<=int(sc.size());k++){
                tab[k][0]=std::max(tab[k][0],sum);
                if(k==int(sc.size()))break;
                tab[k][1]=std::max(tab[k][1],sum+8*sc[k]);
                sum+=12*sc[k];
            }
        }
        return tab;
    }
    void run(){
        for(int h=1;h<32;h+=2)branch(h,0,0);
        const auto left=half(0),right=half(1);
        I king=-(I(1)<<54);
        for(int k=0;k<=26;k++)for(int j=0;j<=1;j++)king=std::max(king,left[k][j]+right[26-k][1-j]);
        std::cout<<label<<" "<<a<<" "<<b<<" "<<claims<<" "<<visits<<" "<<rooted<<" "<<king<<" "<<bestMask<<"\n";
    }
};
int main(int argc,char**argv){
    if(argc!=4)return 1;
    Check c(std::strtoull(argv[1],nullptr,10),std::atoi(argv[2]),std::atoi(argv[3]));
    c.run();
}
