#include <bits/stdc++.h>
using namespace std;
typedef int64_t ll;
typedef uint64_t ull;

const ull n = 1000; // Size of virtual memory
const ull K = 32; // Bucket size
const ull b_sz = 4; // Block size

const ull N = (n + b_sz - 1) / b_sz; // Amount of blocks

extern "C" void initORAM_export(ull* Pos, ull* oram);
extern "C" pair<ull, ull> fetch_export(ull* Pos, ull* oram, ull* res, ull i);
extern "C" void pushDown_export(ull* Pos, ull* oram);

struct NodeElem {
  ull i; // This node has the information of block i
  ull pos; // The leaf corresponding to the NodeElem, or -1 to indicate invalid NodeElem
  array<ull, b_sz> vals; // the actual content of the block i
} __attribute__((packed));

struct Node { // This is a bucket
  array<NodeElem, K> elems;
} __attribute__((packed));

bool isDesOf(ull a, ull b) { // is b a descendent of a
  assert(a != 0);
  assert(b != 0);
  if (b < a) {
    return false;
  }
  ull bits_a = 64 - __builtin_clzll(a);
  ull bits_b = 64 - __builtin_clzll(b);

  ull c = b >> (bits_b - bits_a);
  return a == c;
}

bool checkInvariant(ull* Pos, ull* oram_) {
  Node* oram = (Node*)oram_;

  vector<bool> blocks(N, false); // All blocks should be exactly once somewhere
  for (ull j = 1; j < 2 * N; j++) {
    Node b = oram[j];
    for (ull k = 0; k < K; k++) {
      auto [i, pos, vals] = b.elems[k];
      if (i < N) {
        if (blocks[i]) {
          return false; // Duplicated block
        }
        blocks[i] = true;

        if (!(pos < N)) {
          return false;
        }
        if (!isDesOf(pos + N, j)) {
          return false;
        }

        if (Pos[i] != pos) {
          return false;
        }
      } else if (i != N) {
        return false;
      }
    }
  }

  for(ull i = 0; i < N; i++) {
    if (!blocks[i]) {
      return false; // Missing block
    }
  }

  return true;
}



void test_fetch(ull* Pos, ull* oram_) {
  Node* oram = (Node*)oram_;

  for (ull it = 0; it < 100; it++) {
    ull i = rand() % N;

    NodeElem res;
    auto [j, k] = fetch_export(Pos, oram_, (ull*)(&res), i);
    assert(oram[j].elems[k].i == N);

    oram[j].elems[k] = res;

    assert(checkInvariant(Pos, oram_));
  }
}


int main() {

  for (ull tc = 1; tc < 10000; tc++) {
    cerr << tc << endl;
    Node* oram = new Node[2 * N];
    ull* oram_ = (ull*)oram;
    ull* Pos = new ull[N];

    initORAM_export(Pos, oram_);
    assert(checkInvariant(Pos, oram_));
    test_fetch(Pos, oram_);

    delete[] oram;
    delete[] Pos;
  }
}




