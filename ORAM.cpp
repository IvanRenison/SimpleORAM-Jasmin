#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
typedef unsigned long long ull;


ull random(ull n) {
  return rand() % n;
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


struct ORAM1 {
  static constexpr ull b_sz = 2; // Block size
  static constexpr ull K = 32; // Bucket size
  struct NodeElem {
    ull i; // This node has the information of block i
    ull pos; // The leaf corresponding to the NodeElem, or -1 to indicate invalid NodeElem
    array<ull, b_sz> v; // the actual content of the block i

    NodeElem() {
      i = -1;
      pos = -1;
      v = {0};
    }
  };

  ull n; // Size of the memory
  ull N; // Amount of blocks (N = (n + b_sz - 1) / b_sz)
  vector<ull> Pos; // The leaf corresponding to each block

  vector<array<NodeElem, K>> tree;

  ORAM1(ull n) : n(n), N((n + b_sz - 1) / b_sz), Pos(N), tree(2 * N) {
    for (ull i = 0; i < N; i++) {
      Pos[i] = random(N);
    }
  }

  void check() {
    set<ull> is;
    for (ull i = 1; i < 2 * N; i++) {
      for (ull k = 0; k < K; k++) {
        NodeElem node = tree[i][k];
        if (node.i != -1) {
          assert(!is.count(node.i));
          assert(Pos[node.i] == node.pos);
          is.insert(node.i);
        }
      }
    }
  }

  static void addNode(array<NodeElem, K>& nodes, NodeElem node) {
    for (ull k = 0; k < K; k++) {
      assert(nodes[k].i != node.i);
      if (nodes[k].pos == -1) {
        nodes[k] = node;
        return;
      }
    }
    assert(false);
  }

  NodeElem fetch(ull a) { // Get node elem corresponding to position a
    assert(a < n);
    ull i = a / b_sz;
    ull pos = Pos[i];
    NodeElem ans = NodeElem();

    ull p = pos + N;
    while (p > 0) {
      array<NodeElem, K> this_nodes = tree[p];
      for (ull k = 0; k < K; k++) {
        if (this_nodes[k].i == i) {
          ans = this_nodes[k];
          this_nodes[k] = NodeElem();
        }
      }
      tree[p] = this_nodes;

      p = p / 2;
    }

    return ans;
  }

  void pushDown() {
    ull pos = random(N);

    //cerr << pos << endl;

    pos += N;

    vector<NodeElem> toAdd;
    ull l = 64 - __builtin_clzll(pos);
    assert(pos >> (l - 1) == 1);
    for (ull d = l; d--; ) {
      array<NodeElem, K> this_nodes = tree[pos >> d];

      for (NodeElem node : toAdd) {
        addNode(this_nodes, node);
      }

      toAdd = {};

      if (d > 0) {
        for (ull k = 0; k < K; k++) {
          if (this_nodes[k].i != -1) {
            if (isDesOf(pos >> (d - 1), this_nodes[k].pos + N)) {
              toAdd.push_back(this_nodes[k]);
              this_nodes[k] = NodeElem();
            }
          }
        }
      }

      tree[pos >> d] = this_nodes;
    }
  }

  ull read(ull a) {
    assert(a < n);
    ull i = a / b_sz;

    NodeElem node = fetch(a);

    ull ans = node.v[a % b_sz];

    node.pos = random(N);
    Pos[i] = node.pos;
    if (node.i == -1) {
      node.i = i;
    }

    check();

    addNode(tree[1], node);

    check();

    pushDown();

    return ans;
  }

  void upd(ull a, ull val) {
    assert(a < n);
    ull i = a / b_sz;

    NodeElem node = fetch(a);

    check();

    node.v[a % b_sz] = val;
    node.pos = random(N);
    Pos[i] = node.pos;
    if (node.i == -1) {
      node.i = i;
    }
    addNode(tree[1], node);

    check();

    pushDown();
  }

};



int main() {

  for (ull cas = 0; cas < 100; cas++) {
    cerr << cas << endl;

    ORAM1 oram(8000);
    vector<ull> real(8000);

    for (ull t = 0; t < 10000; t++) {
      bool b = random(2);

      if (b) {
        ull i = random(8000);
        ull val = random(8000);

        oram.upd(i, val);
        real[i] = val;
      } else {
        ull i = random(8000);
        ull val = oram.read(i);
        ull realval = real[i];
        assert(val == realval);
      }

      oram.check();
    }

  }
}

