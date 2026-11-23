// Independent quarter-mask reconstruction. Exclude two complete supports.
#define main broad_census_entry
#include "../upper/bound.cpp"
#undef main
#include <limits>

using Ranked = std::pair<Int,Word>;
using Top = std::array<Ranked,3>;
using TopTable = std::array<std::array<Top,2>,27>;
constexpr Int impossible = std::numeric_limits<Int>::min()/4;

void offer(Top& best, Ranked x) {
    if (x <= best[2]) return;
    best[2] = x;
    if (best[1] < best[2]) std::swap(best[1],best[2]);
    if (best[0] < best[1]) std::swap(best[0],best[1]);
}

TopTable top(const Side& half, Threshold z, Int cap, Int rest, bool isOdd) {
    TopTable table;
    for (auto& row : table) for (auto& cell : row) cell.fill({impossible,0});
    std::uint64_t seen=0;
    for (int i=0; i<int(half.left.masks.size()); ++i) {
        auto l=half.left.masks[i];
        Word left=embed(l,half.parity,4);
        for (int j=0; j<int(half.right.masks.size()); ++j) {
            auto r=half.right.masks[j];
            if ((l || r) && !(half.ev ? r : l)) continue;
            ++seen;
            Word m=left|embed(r,half.parity+2,4);
            const MaskScore local=half.scores(i,j,half.holes(i,j));
            std::array<Int,32> v;
            for (int n=0; n<local.count; ++n)
                v[n]=z.score(local.numerator[n],local.denominator[n]+(isOdd ? 64 : 0));
            std::sort(v.begin(),v.begin()+local.count,std::greater<Int>());
            Int total=0;
            for (int k=0; k<=26 && k<=local.count; ++k) {
                offer(table[k][0],{total,m});
                if (k==local.count) break;
                offer(table[k][1],{total+rest*v[k],m});
                total+=cap*v[k];
            }
        }
    }
    assert(seen==3263443);
    return table;
}

int main() {
    Word w,firstRemoved,secondRemoved;
    Threshold z;
    Int cap,rest;
    if (!(std::cin>>w>>z.a>>z.b>>cap>>rest>>firstRemoved>>secondRemoved)) return 2;
    int ev=preference(w,1,0);
    auto a=top(Side(w,0),z,cap,rest,ev!=0);
    auto b=top(Side(w,1),z,cap,rest,ev!=1);
    Ranked best{impossible,0};
    for (int k=0; k<=26; ++k) for (int j=0; j<=1; ++j) {
        for (auto [x,l] : a[k][j]) for (auto [y,r] : b[26-k][1-j]) {
            Word m=l|r;
            if (x!=impossible && y!=impossible && m!=firstRemoved && m!=secondRemoved)
                best=std::max(best,Ranked{x+y,m});
        }
    }
    std::cout << best.first << ' ' << best.second << '\n';
}
