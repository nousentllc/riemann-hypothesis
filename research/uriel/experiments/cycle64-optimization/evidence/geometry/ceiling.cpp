// C++17. Threshold optimization for the count-only cyclic-tree upper relaxation.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <map>
#include <numeric>
#include <stdexcept>
#include <tuple>
#include <vector>

using Integer = std::int64_t;
struct State {
    int sites, saturated, leftover;
    Integer numerator, denominator;
};
int ceil_div(int x, int d) { return (x+d-1)/d; }

int allowed(int m, int even, int odd, bool reflected) {
    if (!even || !odd) return 0;
    int best = m;
    for (int s=1; s<m; s*=2) {
        const int occupied = ceil_div(even,s) + ceil_div(odd,s) - 1;
        const int count = reflected ? 2*ceil_div(occupied,2) : occupied;
        best = std::min(best,s*count);
    }
    return best;
}

struct Model {
    int width, cap, scale, full, rem;
    bool reflected;
    Model(int n, int a, int b, bool both):
        width(n), cap(a), scale(b), full(n*b/a), rem(n*b%a), reflected(both) {
        if (n<2 || (n&(n-1)) || a<b || b<1) throw std::invalid_argument("parameters");
    }
    std::vector<State> initial() const {
        std::vector<State> s{{0,0,0,0,0},{1,0,0,0,0},{1,1,0,0,cap}};
        if (rem) s.push_back({1,0,1,0,rem});
        return s;
    }
    Integer mass(const State& s) const { return cap*s.saturated + rem*s.leftover; }
    State maximize(Integer num, Integer den) const {
        auto entries=initial();
        auto objective=[&](const State& s) {return den*s.numerator-num*s.denominator;};
        for (int w=2; w<=width; w*=2) {
            const int m=w/2;
            std::vector<int> holes((m+1)*(m+1));
            for (int e=0;e<=m;++e) for(int o=0;o<=m;++o)
                holes[e*(m+1)+o]=m-allowed(m,e,o,reflected);
            std::vector<int> index((w+1)*(full+1)*2,-1);
            std::vector<State> next;
            for(const auto& l:entries) for(const auto& r:entries) {
                if (!l.sites && r.sites) continue;
                int f=l.saturated+r.saturated, t=l.leftover+r.leftover;
                if(f>full || t>bool(rem) || (w==width && (f!=full || t!=bool(rem)))) continue;
                const Integer odd=mass(r);
                State cand{l.sites+r.sites,f,t,l.numerator+r.numerator+
                    2*holes[l.sites*(m+1)+r.sites]*odd,l.denominator+r.denominator+w*odd};
                auto& idx=index[(cand.sites*(full+1)+f)*2+t];
                if(idx<0) {idx=static_cast<int>(next.size()); next.push_back(cand);}
                else if(objective(cand)>objective(next[idx])) next[idx]=cand;
            }
            entries=std::move(next);
        }
        return *std::max_element(entries.begin(),entries.end(),[&](const State& a,const State& b){
            return objective(a)<objective(b);
        });
    }
    void solve() const {
        Integer p=0,q=1, checks=0;
        while(true) {
            State w=maximize(p,q);
            Integer gain=q*w.numerator-p*w.denominator;
            if(gain<0 || !w.denominator) throw std::runtime_error("invalid incumbent");
            ++checks;
            if(!gain) {
                std::cout<<width<<" "<<cap<<" "<<scale<<" "<<reflected<<" "<<p<<" "<<q<<" "<<checks
                         <<" "<<w.numerator<<" "<<w.denominator<<"\n";
                return;
            }
            auto g=std::gcd(w.numerator,w.denominator); p=w.numerator/g; q=w.denominator/g;
        }
    }
};

int main(int argc,char**argv) {
    if(argc!=5) return 1;
    Model(std::stoi(argv[1]),std::stoi(argv[2]),std::stoi(argv[3]),std::stoi(argv[4])!=0).solve();
}
