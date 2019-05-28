struct Node;
struct AdjacencyList;

struct AdjacencyList {
  struct Node * node;
  struct AdjacencyList * next;
};

struct Node {
  int m;
  struct Node * to_copy;
  struct AdjacencyList * adj;
};

void mark(struct Node * x) {
  struct AdjacencyList * l;
  struct Node * subl;
  int root_mark;
  if (x == 0)
    return;
  root_mark = x -> m;
  if (root_mark == 1)
    return;
  x -> m = 1;
  l = x -> adj;
  while (l <> 0) {
    subl = l -> node;
    mark (subl);
  }
}

void copy(struct Node * x) {
  struct AdjacencyList * l;
  struct Node * subl;
  int root_mark;
  if (x == 0)
    return;
  root_mark = x -> m;
  if (root_mark == 1)
    return;
  x -> m = 1;
  l = x -> adj;
  while (l <> 0) {
    subl = l -> node;
    mark (subl);
  }
}

void copy
struct Node * hd;
struct Node n;

int main()
{
  hd = & n;
  n.m = 0;
  n.l = hd;
  n.r = 0;
  mark(hd);
}
