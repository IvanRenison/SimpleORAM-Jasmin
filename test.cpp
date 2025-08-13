#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
typedef unsigned long long ull;

const ull K = 32; // Block size
const ull b_sz = 4; // Block size

extern "C"
void initORAM(ull n, ull* Pos, ull* oram);

struct NodeElem {
  ull i; // This node has the information of block i
  ull pos; // The leaf corresponding to the NodeElem, or -1 to indicate invalid NodeElem
  array<ull, b_sz> v; // the actual content of the block i
} __attribute__((packed));

struct Node {
  array<NodeElem, K> elems;
} __attribute__((packed));


ull calcNBlocks(ull n) {
  return (n + b_sz - 1) / b_sz;
}

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

bool checkInvariant(ull n, ull* Pos, ull* oram_) {
  ull N = calcNBlocks(n);

  Node* oram = (Node*)oram_;


  vector<bool> blocks(N, false); // All blocks should be exactly once somewhere
  for (ull j = 1; j < 2 * N; j++) {
    Node b = oram[j];
    for (ull k = 0; k < K; k++) {
      auto [i, pos, v] = b.elems[k];
      if (i < N) {
        if (blocks[i]) {
          return false; // Duplicated block
        }
        blocks[i] = true;

        if (!(N <= pos && pos < 2 * N)) {
          return false;
        }
        if (!isDesOf(pos, j)) {
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



int main() {

  ull n = 4;
  Node* oram = new Node[2 * calcNBlocks(n)];
  ull* oram_ = (ull*)oram;
  ull* Pos = new ull[calcNBlocks(n)];

  initORAM(n, Pos, oram_);
  assert(checkInvariant(n, Pos, oram_));
}




