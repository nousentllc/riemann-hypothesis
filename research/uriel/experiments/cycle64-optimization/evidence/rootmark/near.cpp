// Filter both half-mask populations by an exact upper on every completion.
#define CYCLE64_CENSUS_LIBRARY
#include "independent.cpp"
#include <map>

using ScoredMask = std::pair<Integer, Word>;
using Candidates = std::array<std::array<std::vector<ScoredMask>,2>,27>;

Candidates survivors(const Census& c, int parity, const Table& opposite) {
    Candidates keep;
    for (Word mask : c.legal(parity,2)) {
        const auto v = c.scores(mask,false);
        Integer total = 0;
        for (int k=0; k<=26 && k<=int(v.size()); ++k) {
            if (total + opposite[26-k][1] > 0) keep[k][0].push_back({total,mask});
            if (k == int(v.size())) break;
            const Integer part = total + c.partial*v[k];
            if (part + opposite[26-k][0] > 0) keep[k][1].push_back({part,mask});
            total += c.cap*v[k];
        }
    }
    return keep;
}

int main() {
    Census c{};
    if (!(std::cin >> c.word >> c.z >> c.scale >> c.cap >> c.partial)) return 2;
    c.minimumPreferred = 2;
    c.initialize();
    for (int h=1; h<32; h+=2) c.searchRoot(h,0,0);
    std::cout << "root " << c.root << ' ' << c.raw << ' ' << c.unique << '\n';
    const auto left = survivors(c,0,c.half(1));
    const auto right = survivors(c,1,c.half(0));
    std::map<Word,Integer> values;
    for (int k=0; k<=26; ++k) for (int j=0; j<=1; ++j) {
        const auto& e = left[k][j];
        const auto& o = right[26-k][1-j];
        if (e.empty() || o.empty()) continue;
        std::uint64_t wins = 0;
        for (auto [a,x] : e) for (auto [b,y] : o) {
            if (a+b <= 0) continue;
            ++wins;
            values[x|y] = std::max(values[x|y],a+b);
        }
        std::cout << "split " << k << ' ' << j << ' ' << e.size() << ' '
                  << o.size() << ' ' << wins << '\n';
    }
    for (auto [support,surplus] : values) std::cout << "support " << support << ' ' << surplus << '\n';
}
