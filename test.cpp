#define _GLIBCXX_DEBUG 1
#define _GLIBCXX_DEBUG_PEDANTIC 1
//#define _GLIBCXX_DEBUG_BACKTRACE 1
#define _GLIBCXX_CONCEPT_CHECKS 1
#define _GLIBCXX_SANITIZE_VECTOR 1
#include <bits/stdc++.h>
using namespace std;
typedef uint8_t u8;
typedef int64_t ll;
typedef uint64_t ull;

const ull n = 256; // Size of virtual memory
const ull K = 32; // Bucket size
const ull b_sz = 4; // Block size
const ull N_queries = 100; // Amount of queries for multi-query operation

const ull N = (n + b_sz - 1) / b_sz; // Amount of blocks

extern "C" u8 initORAM_export(ull* Pos, ull* oram);
extern "C" pair<ull, ull> fetch_export(ull* Pos, ull* oram, ull* res, ull i);
extern "C" u8 pushDown_export(ull* oram);
extern "C" pair<ull, u8> read_write_export(ull* Pos, ull* oram, ull in, ull v, u8 ty);
extern "C" u8 read_write_block_export(ull* Pos, ull* oram, ull* ans, ull i, ull* vs, u8 ty);

struct Query {
  ull ty; // 0 for only read, 1 for read and write
  ull in; // index in the virtual memory
  ull v;  // value to write if ty = 1
} __attribute__((packed));

extern "C" u8 multiQuery_export(ull* Pos, ull* oram, ull* ans, Query* queries);

struct QueryBlock {
  ull ty;              // 0 for only read, 1 for read and write
  ull i;               // block index
  array<ull, b_sz> v;  // values to write if ty = 1
} __attribute__((packed));;

extern "C" u8 multiQuery_blocks_export(ull* Pos, ull* oram, ull* ans, QueryBlock* queries);


struct NodeElem {
  ull i; // This node has the information of block i, or N to indicate invalid NodeElem
  ull pos; // The leaf corresponding to the NodeElem
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

void addToNode(Node& node, NodeElem elem) {
  for (ull k = 0; k < K; k++) {
    assert(node.elems[k].i != elem.i);
    if (node.elems[k].i == N) {
      node.elems[k] = elem;
      return;
    }
  }
  assert(false);
}

bool checkInvariant(ull* Pos, ull* oram_, array<ull, n> real_mem) {
  Node* oram = (Node*)oram_;

  vector<bool> blocks(N, false); // All blocks should be exactly once somewhere
  for (ull ix = 1; ix < 2 * N; ix++) {
    Node b = oram[ix];
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
        if (!isDesOf(ix, pos + N)) {
          return false;
        }

        if (Pos[i] != pos) {
          return false;
        }

        for (ull j = 0; j < b_sz; j++) {
          if (i * b_sz + j < n) {
            assert(vals[j] == real_mem[i * b_sz + j]);
          } else {
            assert(vals[j] == 0);
          }
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


void test_fetch(ull* Pos, ull* oram_, array<ull, n> real_mem) {
  Node* oram = (Node*)oram_;

  for (ull it = 0; it < 100; it++) {
    ull i = rand() % N;

    NodeElem res;
    auto [j, k] = fetch_export(Pos, oram_, (ull*)(&res), i);
    assert(oram[j].elems[k].i == N);
    assert(res.i == i);
    assert(res.pos < N);
    assert(isDesOf(j, res.pos + N));

    oram[j].elems[k] = res;

    assert(checkInvariant(Pos, oram_, real_mem));
  }
}

void test_fetch_and_pushDown(ull* Pos, ull* oram_, array<ull, n> real_mem) {
  Node* oram = (Node*)oram_;

  for (ull it = 0; it < 100; it++) {
    ull i = rand() % N;

    NodeElem res;
    auto [j, k] = fetch_export(Pos, oram_, (ull*)(&res), i);
    assert(oram[j].elems[k].i == N);
    assert(res.i == i);
    assert(res.pos < N);
    assert(isDesOf(j, res.pos + N));

    addToNode(oram[1], res);

    assert(checkInvariant(Pos, oram_, real_mem));
    pushDown_export(oram_);
    assert(checkInvariant(Pos, oram_, real_mem));
  }
}

void test_empty_read(ull* Pos, ull* oram_, array<ull, n> real_mem) {
  for (ull it = 0; it < 100; it++) {
    ull in = rand() % n;

    auto [val, _] = read_write_export(Pos, oram_, in, 0, 0);
    assert(val == 0);

    assert(checkInvariant(Pos, oram_, real_mem));
  }
}



int main() {

  for (ull tc = 0; tc < 100; tc++) {
    cerr << tc << endl;
    Node* oram = new Node[2 * N];
    ull* oram_ = (ull*)oram;

    ull* Pos = new ull[N];

    array<ull, n> mem = {0};

    initORAM_export(Pos, oram_);
    assert(checkInvariant(Pos, oram_, mem));
    test_fetch(Pos, oram_, mem);
    test_fetch_and_pushDown(Pos, oram_, mem);
    test_empty_read(Pos, oram_, mem);

    delete[] oram;
    delete[] Pos;
  }

  cerr << "First part done" << endl;

  for (ull tc = 0; tc < 100; tc++) {
    cerr << tc << endl;

    Node* oram = new Node[2 * N];
    ull* oram_ = (ull*)oram;
    ull* Pos = new ull[N];

    array<ull, n> mem = {0};

    initORAM_export(Pos, oram_);
    assert(checkInvariant(Pos, oram_, mem));

    for (ull it = 0; it < 1000; it++) {
      ull in = rand() % n;

      ull t = rand() % 2;

      if (t) { // Read
        auto [v, _] = read_write_export(Pos, oram_, in, 0, 0);
        assert(v == mem[in]);
        assert(checkInvariant(Pos, oram_, mem));
      } else { // Write
        ull v = rand();
        auto [v2, _] = read_write_export(Pos, oram_, in, v, 1);
        assert(v2 == mem[in]);
        mem[in] = v;
        assert(checkInvariant(Pos, oram_, mem));
      }
    }

    delete[] oram;
    delete[] Pos;
  }

  cerr << "Second part done" << endl;

  for (ull tc = 0; tc < 100; tc++) {
    cerr << tc << endl;

    Node* oram = new Node[2 * N];
    ull* oram_ = (ull*)oram;
    ull* Pos = new ull[N];

    array<ull, n> mem = {0};

    initORAM_export(Pos, oram_);
    assert(checkInvariant(Pos, oram_, mem));

    Query* queries = new Query[N_queries];
    ull* ans = new ull[N_queries];
    ull* real_ans = new ull[N_queries];

    for (ull q = 0; q < N_queries; q++) {
      ull in = rand() % n;

      ull t = rand() % 2;

      if (t) { // Read
        queries[q] = {0, in, 0};
        real_ans[q] = mem[in];
      } else { // Write
        ull v = rand();
        queries[q] = {1, in, v};
        real_ans[q] = mem[in];
        mem[in] = v;
      }
    }

    multiQuery_export(Pos, oram_, ans, queries);
    assert(checkInvariant(Pos, oram_, mem));
    for (ull q = 0; q < N_queries; q++) {
      assert(ans[q] == real_ans[q]);
    }

    delete[] oram;
    delete[] Pos;
    delete[] queries;
    delete[] ans;
    delete[] real_ans;
  }

  cerr << "Third part done" << endl;

  for (ull tc = 0; tc < 100; tc++) {
    cerr << tc << endl;

    Node* oram = new Node[2 * N];
    ull* oram_ = (ull*)oram;
    ull* Pos = new ull[N];

    array<ull, n> mem = {0};

    initORAM_export(Pos, oram_);
    assert(checkInvariant(Pos, oram_, mem));

    for (ull it = 0; it < 1000; it++) {
      ull in = rand() % n;
      ull i = in / b_sz;

      ull t = rand() % 2;

      ull* vs = new ull[b_sz];
      ull* ans = new ull[b_sz];
      if (t) { // Read
        read_write_block_export(Pos, oram_, ans, i, vs, 0);
        for (ull j = 0; j < b_sz; j++) {
          ull idx = i * b_sz + j;
          if (idx < n) {
            assert(ans[j] == mem[idx]);
          } else {
            assert(ans[j] == 0);
          }
        }
        assert(checkInvariant(Pos, oram_, mem));
      } else { // Write
        for (ull j = 0; j < b_sz; j++) {
          ull idx = i * b_sz + j;
          if (idx < n) {
            vs[j] = rand();
          }
        }
        read_write_block_export(Pos, oram_, ans, i, vs, 1);
        for (ull j = 0; j < b_sz; j++) {
          ull idx = i * b_sz + j;
          if (idx < n) {
            assert(ans[j] == mem[idx]);
            mem[idx] = vs[j];
          } else {
            assert(ans[j] == 0);
          }
        }
      }

      delete [] vs;
      delete [] ans;
    }

    delete[] oram;
    delete[] Pos;
  }

  cerr << "Fourth part done" << endl;

  for (ull tc = 0; tc < 100; tc++) {
    cerr << tc << endl;

    Node* oram = new Node[2 * N];
    ull* oram_ = (ull*)oram;
    ull* Pos = new ull[N];

    array<ull, n> mem = {0};

    initORAM_export(Pos, oram_);
    assert(checkInvariant(Pos, oram_, mem));

    QueryBlock* queries = new QueryBlock[N_queries];
    array<ull, b_sz>* ans = new array<ull, b_sz>[N_queries];
    array<ull, b_sz>* real_ans = new array<ull, b_sz>[N_queries];

    for (ull q = 0; q < N_queries; q++) {
      ull in = rand() % n;
      ull i = in / b_sz;

      ull t = rand() % 2;

      if (t) { // Read
        queries[q] = {0, i, {}};
        for (ull j = 0; j < b_sz; j++) {
          ull idx = i * b_sz + j;
          if (idx < n) {
            real_ans[q][j] = mem[idx];
          } else {
            real_ans[q][j] = 0;
          }
        }
      } else { // Write
        queries[q] = {1, i, {}};
        for (ull j = 0; j < b_sz; j++) {
          ull idx = i * b_sz + j;
          if (idx < n) {
            ull v = rand();
            queries[q].v[j] = v;
            real_ans[q][j] = mem[idx];
            mem[idx] = v;
          } else {
            real_ans[q][j] = 0;
          }
        }
      }
    }

    multiQuery_blocks_export(Pos, oram_, (ull*)ans, queries);

    assert(checkInvariant(Pos, oram_, mem));

    for (ull q = 0; q < N_queries; q++) {
      for (ull j = 0; j < b_sz; j++) {
        assert(ans[q][j] == real_ans[q][j]);
      }
    }

    delete[] oram;
    delete[] Pos;
    delete[] queries;
    delete[] ans;
    delete[] real_ans;
  }

}




