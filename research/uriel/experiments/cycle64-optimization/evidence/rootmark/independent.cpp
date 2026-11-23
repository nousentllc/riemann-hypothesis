// Independent support enumeration for a priced, capped 64-cycle.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <limits>
#include <vector>

using Word = std::uint64_t;
using Integer = std::int64_t;
using Table = std::array<std::array<Integer, 2>, 27>;
constexpr Integer emptyValue = std::numeric_limits<Integer>::min() / 4;

int count(Word word) { return __builtin_popcountll(word); }
int first(Word word) { return __builtin_ctzll(word); }
Word single(int leaf) { return Word{1} << leaf; }
Word rotate(Word sites, int step) { return (sites << step) | (sites >> (64 - step)); }

struct Node {
    Word members = 0;
    Word other = 0;
    int stride = 0;
};

struct Census {
    Word word;
    Integer z, scale, cap, partial;
    int minimumPreferred;
    std::array<Integer,64> price{}, denominator{};
    std::array<Word,64> prerequisites{}, dependents{};
    std::vector<Node> nodes;
    Integer root = emptyValue;
    std::uint64_t raw = 0, unique = 0;

    int choice(int c, int s) const { return int(word >> (s - 1 + c) & 1); }

    void initialize() {
        for (int s = 1; s < 64; s *= 2) {
            for (int c = 0; c < s; ++c) {
                int anchor = c;
                for (int stride = s; stride < 64; stride *= 2)
                    anchor += stride * choice(anchor, stride);
                Node node;
                node.stride = s;
                for (int t = c; t < 64; t += s) {
                    node.members |= single(t);
                    prerequisites[t] |= single(anchor);
                    if ((t / s) % 2 != choice(c,s)) {
                        node.other |= single(t);
                        denominator[t] += 64 / s;
                    }
                }
                nodes.push_back(node);
            }
        }
        for (int t = 0; t < 64; ++t) {
            prerequisites[t] |= single(t);
            ++denominator[t];
            for (Word u = prerequisites[t]; u; u &= u - 1)
                dependents[first(u)] |= single(t);
        }
    }

    std::vector<Integer> scores(Word mask, bool includeRoot) const {
        std::array<Integer,64> gain{};
        for (const auto& node : nodes) {
            const int s = node.stride;
            Word active = mask & node.members;
            Word target = mask & node.other;
            if (!target || s == 32 || (s == 1 && !includeRoot) || count(active) > 32 / s)
                continue;
            int missing = 0;
            for (int step = s; step < 64; step += 2*s)
                missing += !(active & rotate(active, step));
            for (; target; target &= target-1) gain[first(target)] += 2*missing;
        }
        std::vector<Integer> values;
        for (; mask; mask &= mask-1) {
            int t = first(mask);
            values.push_back(scale*gain[t] - z*denominator[t] + price[t]);
        }
        std::sort(values.begin(), values.end(), std::greater<Integer>());
        return values;
    }

    // Every retained leaf forces its ancestors' preferred minima. Excluding a
    // leaf therefore excludes each leaf whose prerequisite set contains it.
    void searchRoot(int step, Word retained, Word excluded) {
        if (count(~excluded) < 27) return;
        Word free = ~(retained | excluded);
        if (!free) {
            const Word other = nodes.front().other;
            if (!(retained & other) || count(retained & ~other) < minimumPreferred) return;
            ++raw;
            for (int smaller = 1; smaller < step; smaller += 2)
                if (!(retained & rotate(retained,smaller))) return;
            ++unique;
            auto v = scores(retained,true);
            Integer total = partial*v[26];
            for (int k = 0; k < 26; ++k) total += cap*v[k];
            root = std::max(root,total);
            return;
        }
        int leaf = first(free);
        searchRoot(step, retained, excluded | dependents[leaf]);
        Word add = prerequisites[leaf] & ~retained;
        if (add & excluded) return;
        Word together = retained | add;
        Word neighbours = rotate(add,step) | rotate(add,64-step);
        if (together & neighbours) return;
        for (; neighbours; neighbours &= neighbours-1) excluded |= dependents[first(neighbours)];
        if (!(together & excluded)) searchRoot(step,together,excluded);
    }

    std::vector<Word> legal(int c, int s) const {
        if (s == 64) return {0, single(c)};
        int d = choice(c,s);
        auto yes = legal(c+s*d,2*s);
        auto other = legal(c+s*(1-d),2*s);
        std::vector<Word> masks{0};
        masks.reserve(1+(yes.size()-1)*other.size());
        for (Word m : yes) if (m)
            for (Word n : other) masks.push_back(m|n);
        return masks;
    }

    Table half(int parity) const {
        Table opt;
        for (auto& row : opt) row.fill(emptyValue);
        auto masks = legal(parity,2);
        assert(masks.size() == 3263443);
        for (Word m : masks) {
            auto v = scores(m,false);
            Integer total = 0;
            for (int k=0; k<=26 && k<=int(v.size()); ++k) {
                opt[k][0] = std::max(opt[k][0],total);
                if (k == int(v.size())) break;
                opt[k][1] = std::max(opt[k][1],total+partial*v[k]);
                total += cap*v[k];
            }
        }
        return opt;
    }

    void run() {
        initialize();
        for (int step=1; step<32; step+=2) searchRoot(step,0,0);
        auto left=half(0), right=half(1);
        Integer uncredited=emptyValue;
        for (int k=0; k<=26; ++k) for (int j=0; j<=1; ++j)
            uncredited=std::max(uncredited,left[k][j]+right[26-k][1-j]);
        std::cout << root << ' ' << uncredited << ' ' << raw << ' ' << unique << '\n';
    }
};


#ifndef CYCLE64_CENSUS_LIBRARY
int main() {
    Census c{};
    if (!(std::cin >> c.word >> c.z >> c.scale >> c.cap >> c.partial >> c.minimumPreferred)) return 2;
    if ((c.word >> 63) || c.z<0 || c.scale<=0 || c.partial<=0 || c.partial>=c.cap) return 3;
    for (auto& p : c.price) if (!(std::cin >> p)) return 4;
    c.run();
}
#endif
