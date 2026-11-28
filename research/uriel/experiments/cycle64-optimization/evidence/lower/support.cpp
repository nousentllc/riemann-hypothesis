// Optimize two independently labeled sixteen-leaf subtrees on an integer rate
// grid.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <vector>
using namespace std;
constexpr int U = 8, CAP = 19, M = 16 * CAP, NEVER = -100000000;
struct Floor {
  int b, h, need;
};
struct Shape {
  int mask, n;
  vector<Floor> floors;
};
vector<Shape> shapes;
int missing[17][65536];
constexpr int leaf_min = 1;
int table[65][513]{};
int capfloor(int width, int active) { return table[width][active * CAP]; }
bool mark(int total, int even, int width) {
  return total > 0 && total <= 512 && table[width][total] > 0 &&
         even >= table[width][total];
}
bool singlePath(int mass) {
  return mark(mass, mass, 2) && mark(mass, mass, 4) && mark(mass, mass, 8);
}
int cnt(int a) { return __builtin_popcount((unsigned)a); }
vector<vector<int>> orders(int w) {
  if (w == 1)
    return {{0}};
  auto half = orders(w / 2);
  vector<vector<int>> out;
  for (const auto &a : half)
    for (const auto &b : half)
      for (int parity : {0, 1}) {
        vector<int> x;
        for (int v : a)
          x.push_back(2 * v + parity);
        for (int v : b)
          x.push_back(2 * v + 1 - parity);
        out.push_back(x);
      }
  return out;
}
// Only an occupied node needs an even-mass floor. Use the worst total
// permitted by this support, allowing any later greedy increase in its rates.
void init() {
  for (int w : {2, 4, 8, 16})
    for (int t = 0; t < (1 << w); t++) {
      for (int h = 1; h < w; h += 2) {
        unsigned rot =
            ((unsigned(t) << h) | (unsigned(t) >> (w - h))) & ((1u << w) - 1);
        if (!(rot & t))
          missing[w][t]++;
      }
    }
  for (int mask = 1; mask < 65536; mask++) {
    Shape s{mask, cnt(mask), {}};
    bool valid = true;
    for (int w : {2, 4, 8, 16})
      for (int b = 0; b < 16; b += w) {
        int m = (mask >> b) & ((1 << w) - 1);
        if (!m)
          continue;
        int ne = cnt(m & ((1 << (w / 2)) - 1)), minmass = capfloor(w, cnt(m));
        if (ne * CAP < minmass) {
          valid = false;
          break;
        }
        s.floors.push_back({b, w / 2, minmass});
      }
    if (valid)
      shapes.push_back(s);
  }
}
struct Panel {
  array<int, M + 1> val;
  Panel() { val.fill(NEVER); }
};
int PN = 11, QD = 100; // target PN/QD
int envelope[2][M + 1], denseCost[513], denseSplit[513], evC[2][M + 1],
    odC[2][M + 1];
struct Win {
  int value = NEVER, mode = -1, mass = 0, mask = 0, h = 0;
};
array<Win, 8> chartwin;
Win oneTip;
int focusStep = -1;
int sparseTable[2][M + 1];
// At a fixed support the local threshold margin is linear in every tick.
// Mandatory laminar floors are met from leaves to root, then the remaining
// ticks are offered in decreasing order of marginal value.
array<int, 16> replayRates{};
Panel evaluate(const vector<int> &co, bool sparse, int requestedMass = -1,
               int requestedMask = 0) {
  Panel best;
  for (const auto &s : shapes) {
    int mask = s.mask, raw = 0;
    if (requestedMask && requestedMask != mask)
      continue;
    for (int i = 0; i < 16; i++)
      if (mask >> i & 1)
        raw |= 1 << co[i];
    array<int, 16> cf{};
    vector<int> priority;
    for (int i = 0; i < 16; i++)
      if (mask >> i & 1) {
        cf[i] = -PN * (1 + 2 * i);
        priority.push_back(i);
      }
    for (int w : {2, 4, 8, 16})
      for (int b = 0; b < 16; b += w) {
        if (!(mask & (((1 << w) - 1) << b)))
          continue;
        int sub = 0;
        for (int i = b; i < b + w; i++)
          if (mask >> i & 1)
            sub |= 1 << (co[i] / (16 / w));
        int inc = 2 * QD * missing[w][sub];
        for (int i = b + w / 2; i < b + w; i++)
          cf[i] += inc;
      }
    stable_sort(priority.begin(), priority.end(),
                [&](int a, int b) { return cf[a] > cf[b]; });
    array<int, 16> rates{};
    for (int i : priority)
      rates[i] = leaf_min;
    for (const auto &f : s.floors) {
      int left = f.need -
                 accumulate(rates.begin() + f.b, rates.begin() + f.b + f.h, 0);
      if (left <= 0)
        continue;
      for (int i : priority)
        if (f.b <= i && i < f.b + f.h) {
          int z = min(left, CAP - rates[i]);
          rates[i] += z;
          left -= z;
          if (!left)
            break;
        }
      if (left)
        abort();
    }
    int mass = accumulate(rates.begin(), rates.end(), 0),
        val = inner_product(rates.begin(), rates.end(), cf.begin(), 0);
    int lo = mass;
    array<int, M + 1> curve;
    auto offer = [&]() {
      curve[mass] = val;
      if (!sparse && val > best.val[mass]) {
        best.val[mass] = val;
        if (mass == requestedMass)
          replayRates = rates;
      }
    };
    offer();
    for (int i : priority) {
      while (rates[i] < CAP) {
        mass++;
        val += cf[i];
        rates[i]++;
        offer();
      }
    }
    if (!sparse)
      continue;
    int rev = 0;
    for (int i = 0; i < 16; i++)
      if (raw >> i & 1)
        rev |= 1 << (15 - i);
    // On the odd parent, blocked steps are complementary to the union of
    // D and its reflection; a second tip adds one translate and its reflection.
    int h1 = 16 - cnt(raw | rev);
    array<Win, 17> opt2;
    Win opt1;
    auto search = [&](int k, int h) {
      Win t;
      int slope = 2 * QD * h - 96 * PN;
      for (int d = lo; d <= mass; d++) {
        if (focusStep >= 0)
          sparseTable[k][d] = max(sparseTable[k][d], curve[d] + slope * d);
        if (envelope[k][d] == NEVER)
          continue;
        int v = curve[d] + slope * d + envelope[k][d];
        if (v > t.value)
          t = {v, k, d, mask, h};
      }
      return t;
    };
    opt1 = search(0, h1);
    if (opt1.value > oneTip.value)
      oneTip = opt1;
    for (int z = 0; z < 8; z++) {
      if (focusStep >= 0 && z != focusStep)
        continue;
      int step = 1 + 2 * z,
          shift = ((unsigned(raw) >> step) | (unsigned(raw) << (16 - step))) &
                  65535;
      int backward = 0;
      for (int j = 0; j < 16; j++)
        if (shift >> j & 1)
          backward |= 1 << (15 - j);
      int h2 = 16 - cnt(raw | rev | shift | backward);
      if (opt2[h2].mode < 0)
        opt2[h2] = search(1, h2);
      auto r = opt1.value > opt2[h2].value ? opt1 : opt2[h2];
      if (r.value > chartwin[z].value)
        chartwin[z] = r;
    }
  }
  return best;
}
#include "residual.hpp"

int main(int argc, char **argv) {
  PN = argc > 1 ? atoi(argv[1]) : 11;
  QD = argc > 2 ? atoi(argv[2]) : 100;
  assert(QD > 0 && QD <= 10000 && PN >= 0 && PN <= 1100);
  int tw, tm, tf;
  while (cin >> tw >> tm >> tf)
    table[tw][tm] = tf;
  init();
  auto all = orders(16);
  array<int, M + 1> low{}, lowOrder{};
  map<array<int, M + 1>, vector<int>> distinctDense;
  low.fill(100000000);
  for (int j = 0; j < (int)all.size(); j++)
    if (all[j][0] == 0 && all[j][8] == 1) {
      auto p = evaluate(all[j], false);
      distinctDense[p.val].push_back(j);
      for (int i = 1; i <= M; i++)
        if (p.val[i] < low[i]) {
          low[i] = p.val[i];
          lowOrder[i] = j;
        }
    }
  for (int e = 1; e <= 512; e++) {
    int v = NEVER, spl = -1;
    for (int a = 1; a <= M; a++) {
      int b = e - a;
      if (b < 1 || b > M || low[a] == NEVER || low[b] == NEVER ||
          !mark(e, a, 32))
        continue;
      int z = low[a] + low[b] - 32 * PN * b;
      if (z > v) {
        v = z;
        spl = a;
      }
    }
    denseCost[e] = v;
    denseSplit[e] = spl;
  }
  for (int k = 0; k < 2; k++)
    for (int d = 1; d <= M; d++) {
      int best = NEVER;
      for (int c0 = 1; c0 <= CAP; c0++)
        for (int c1 = k ? 1 : 0; c1 <= (k ? CAP : 0); c1++) {
          int c = c0 + c1, e = 64 * U - d - c;
          if (e < 1 || denseCost[e] == NEVER || !mark(64 * U, e, 64) ||
              !mark(c + d, c, 32) || !mark(c, c0, 16) || !singlePath(c0) ||
              (c1 && !singlePath(c1)))
            continue;
          int sc = denseCost[e] - 65 * PN * c0 + (12 * QD - 81 * PN) * c1;
          if (sc > best) {
            best = sc;
            evC[k][d] = c0;
            odC[k][d] = c1;
          }
        }
      envelope[k][d] = best;
    }
  int worst = 100000000, wi = 0, wz = 0, singlePass = 0, eitherPass = 0,
      newMasks = 0, charts = 0;
  vector<pair<int, int>> missed;
  Win w, replay;
  int rj = -1, rz = -1;
  vector<int> old = {0x070f, 0x0331, 0x07d1, 0x0d71, 0x3101, 0x5101,
                     0xd107, 0x1301, 0x0d11, 0x1501, 0xd101};
  for (int j = 0; j < (int)all.size(); j++)
    if (!all[j][0]) {
      oneTip = Win{};
      chartwin = {};
      evaluate(all[j], true);
      for (int z = 0; z < 8; z++) {
        auto res = chartwin[z];
        charts++;
        if (res.value < 0)
          missed.emplace_back(j, z);
        singlePass += (oneTip.value >= 0);
        if (rj < 0 && oneTip.value < 0 && res.value >= 0) {
          rj = j;
          rz = z;
          replay = res;
        }
        eitherPass += (res.value >= 0);
        newMasks += (res.value >= 0 &&
                     find(old.begin(), old.end(), res.mask) == old.end());
        if (res.value < worst) {
          worst = res.value;
          wi = j;
          wz = z;
          w = res;
        }
      }
    }
  int d = w.mass, c0 = evC[w.mode][d], c1 = odC[w.mode][d],
      e = 512 - d - c0 - c1;
  assert(rj >= 0);
  int rd = replay.mass, rc0 = evC[replay.mode][rd], rc1 = odC[replay.mode][rd],
      re = 512 - rd - rc0 - rc1;
  int ra = denseSplit[re], rb = re - ra, step = 2 * rz + 1;
  array<int, 64> physical{}, profile{};
  for (int block : {0, 1, 3}) {
    int m = block == 0 ? ra : block == 1 ? rb : rd;
    int order = block == 3 ? rj : lowOrder[m];
    evaluate(all[order], false, m, block == 3 ? replay.mask : 0);
    for (int i = 0; i < 16; i++) {
      physical[16 * block + i] = 4 * all[order][i] + (block == 0   ? 0
                                                      : block == 1 ? 2
                                                                   : 3);
      profile[16 * block + i] = replayRates[i];
    }
  }
  for (int i = 0; i < 16; i++) {
    int j = i % 8, bitRev = 4 * (j & 1) + (j & 2) + (j >> 2);
    int coord = (2 * bitRev + (i >= 8 ? step : 0)) % 16;
    physical[32 + i] = 4 * coord + 1;
    profile[32 + i] = i == 0 ? rc0 : i == 8 ? rc1 : 0;
  }
  auto printArray = [](const auto &xs) {
    cout << "[";
    bool first = true;
    for (int x : xs) {
      if (!first)
        cout << ",";
      cout << x;
      first = false;
    }
    cout << "]";
  };
  vector<array<int, 7>> joint;
  if (PN == 1012 && QD == 10000)
    for (auto [j, z] : missed) {
      focusStep = z;
      for (auto &row : sparseTable)
        fill(begin(row), end(row), NEVER);
      evaluate(all[j], true);
      int sparseByE[513];
      fill(begin(sparseByE), end(sparseByE), NEVER);
      for (int k = 0; k < 2; k++)
        for (int md = 1; md <= M; md++)
          if (sparseTable[k][md] != NEVER)
            for (int c0 = 1; c0 <= CAP; c0++)
              for (int c1 = k ? 1 : 0; c1 <= (k ? CAP : 0); c1++) {
                int c = c0 + c1, e = 512 - c - md;
                if (e < 1 || !mark(512, e, 64) || !mark(c + md, c, 32) ||
                    !mark(c, c0, 16) || !singlePath(c0) ||
                    (c1 && !singlePath(c1)))
                  continue;
                int v = sparseTable[k][md] - 65 * PN * c0 +
                        (12 * QD - 81 * PN) * c1;
                sparseByE[e] = max(sparseByE[e], v);
              }
      vector<array<int, 3>> options;
      for (int a = 1; a <= M; a++)
        for (int b = 1; b <= M; b++) {
          int e = a + b;
          if (e > 512 || sparseByE[e] == NEVER || !mark(e, a, 32))
            continue;
          options.push_back({a, b, sparseByE[e] - 32 * PN * b});
        }
      int pass = 0;
      set<int> missedA, missedB;
      for (const auto &[av, acount] : distinctDense)
        for (const auto &[bv, bcount] : distinctDense) {
          bool found = false;
          for (auto [a, b, v] : options)
            if (av[a] != NEVER && bv[b] != NEVER && av[a] + bv[b] + v >= 0) {
              found = true;
              break;
            }
          if (found)
            pass += acount.size() * bcount.size();
          else {
            missedA.insert(acount.begin(), acount.end());
            missedB.insert(bcount.begin(), bcount.end());
          }
        }
      joint.push_back({j, 2 * z + 1, pass, int(missedA.size()),
                       int(missedB.size()),
                       missedA.empty() ? -1 : *missedA.begin(),
                       missedB.empty() ? -1 : *missedB.begin()});
    }
  focusStep = -1;
  cout << "{\"target\":\"" << PN << "/" << QD << "\",\"charts\":" << charts
       << ",\"local_shapes\":" << shapes.size()
       << ",\"single_pass\":" << singlePass << ",\"either_pass\":" << eitherPass
       << ",\"passing_best_uses_new_D_mask\":" << newMasks
       << ",\"minimum_integer_margin\":" << worst << ",\"worst_order\":" << wi
       << ",\"worst_step\":" << 2 * wz + 1 << ",\"worst_mask\":" << w.mask
       << ",\"worst_missing_steps\":" << w.h << ",\"worst_mass_ticks\":["
       << denseSplit[e] << "," << e - denseSplit[e] << "," << c0 << "," << c1
       << "," << d << "],\"rescued_witness\":{\"chart\":" << rj
       << ",\"step\":" << step << ",\"lower_integer_margin\":" << replay.value
       << ",\"physical_order\":";
  printArray(physical);
  cout << ",\"rate_ticks_in_tree_order\":";
  printArray(profile);
  cout << "},\"distinct_dense_curves\":" << distinctDense.size()
       << ",\"full_dense_cross_on_coarse_misses\":[";
  bool first = true;
  for (auto row : joint) {
    if (!first)
      cout << ",";
    printArray(row);
    first = false;
  }
  cout << "],\"wider_residual\":[";
  if (PN == 1012 && QD == 10000) {
    first = true;
    for (auto row : wideResidual(all, low)) {
      if (!first)
        cout << ",";
      printArray(row);
      first = false;
    }
  }
  cout << "]}" << endl;
}
