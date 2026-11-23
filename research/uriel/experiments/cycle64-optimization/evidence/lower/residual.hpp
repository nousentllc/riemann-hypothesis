// Extra support test on the last three normalized (D, step) configurations.
// This header uses the exact floor table and width-16 shape list from
// support.cpp.
struct LocalChoice {
  int physical = 0, size = 0, unitMargin = 0;
  array<int, 16> cross{};
  vector<int> minimumTicks;
};

vector<LocalChoice> localChoices(const vector<int> &order, int maxSize) {
  vector<LocalChoice> out;
  for (const Shape &shape : shapes) {
    if (shape.n > maxSize)
      continue;
    LocalChoice choice;
    choice.size = shape.n;
    for (int i = 0; i < 16; i++)
      if (shape.mask >> i & 1) {
        choice.physical |= 1 << order[i];
        choice.unitMargin -= PN * (1 + 2 * i);
      }
    for (int w : {2, 4, 8, 16})
      for (int b = 0; b < 16; b += w) {
        int sub = 0, odd = 0;
        for (int i = b; i < b + w; i++)
          if (shape.mask >> i & 1) {
            sub |= 1 << (order[i] / (16 / w));
            odd += (i >= b + w / 2);
          }
        choice.unitMargin += 2 * QD * missing[w][sub] * odd;
      }
    for (int minimum = 1; minimum <= CAP; minimum++) {
      bool valid = true;
      for (int w : {2, 4, 8, 16})
        for (int b = 0; b < 16; b += w) {
          int occupied = (shape.mask >> b) & ((1 << w) - 1);
          if (!occupied)
            continue;
          int discount = b == 0 ? CAP - minimum : 0;
          int total = cnt(occupied) * CAP - discount;
          int even = cnt(occupied & ((1 << (w / 2)) - 1)) * CAP - discount;
          if (!mark(total, even, w))
            valid = false;
        }
      if (valid)
        choice.minimumTicks.push_back(minimum);
    }
    for (int t = 0; t < 16; t++) {
      unsigned raw = choice.physical;
      int forward = ((raw >> t) | (raw << (16 - t))) & 65535, back = 0;
      for (int i = 0; i < 16; i++)
        if (forward >> i & 1)
          back |= 1 << (15 - i);
      choice.cross[t] = forward | back;
    }
    out.push_back(choice);
  }
  return out;
}

using ResidualRow = array<int, 5>;
vector<ResidualRow> wideResidual(const vector<vector<int>> &all,
                                 const array<int, M + 1> &denseALower) {
  const auto bPanel = evaluate(all[11776], false);
  array<int, 513> dense;
  dense.fill(NEVER);
  for (int a = 1; a <= M; a++)
    for (int b = 1; b <= M; b++) {
      if (a + b > 512 || denseALower[a] == NEVER || bPanel.val[b] == NEVER ||
          !mark(a + b, a, 32))
        continue;
      dense[a + b] =
          max(dense[a + b], denseALower[a] + bPanel.val[b] - 32 * PN * b);
    }
  const auto dChoices = localChoices(all[10320], 9);
  map<int, array<int, CAP + 1>> byPhysicalC;
  array<int, 16> covered{}, total{}, worst{}, best{};
  worst.fill(-NEVER);
  best.fill(NEVER);
  for (const auto &cOrder : all) {
    int step = cOrder[8];
    if (cOrder[0] || (step != 3 && step != 5 && step != 7))
      continue;
    int largest = NEVER;
    for (const auto &c : localChoices(cOrder, 8)) {
      auto [entry, inserted] = byPhysicalC.try_emplace(c.physical);
      auto &boundary = entry->second;
      if (inserted) {
        boundary.fill(NEVER);
        for (const auto &d : dChoices) {
          int used = 0;
          for (int i = 0; i < 16; i++)
            if (c.physical >> i & 1)
              used |= d.cross[i];
          int holes = 16 - cnt(used);
          for (int d0 : d.minimumTicks) {
            int dm = (d.size - 1) * CAP + d0;
            int localD = d.unitMargin * CAP + PN * (CAP - d0) +
                         (2 * QD * holes - 96 * PN) * dm;
            for (int c0 = 1; c0 <= CAP; c0++) {
              int cm = (c.size - 1) * CAP + c0, e = 512 - cm - dm;
              if (e <= 0 || dense[e] == NEVER || !mark(512, e, 64) ||
                  !mark(cm + dm, cm, 32))
                continue;
              boundary[c0] =
                  max(boundary[c0],
                      dense[e] + localD - 64 * PN * cm + PN * (CAP - c0));
            }
          }
        }
      }
      for (int c0 : c.minimumTicks)
        if (boundary[c0] != NEVER)
          largest = max(largest, c.unitMargin * CAP + boundary[c0]);
    }
    total[step]++;
    covered[step] += (largest >= 0);
    worst[step] = min(worst[step], largest);
    best[step] = max(best[step], largest);
  }
  vector<ResidualRow> out;
  for (int step : {3, 5, 7})
    out.push_back({step, total[step], covered[step], worst[step], best[step]});
  return out;
}
