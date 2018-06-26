
#define NULL 0

int f1() {
  int *p = nullptr;
  p = nullptr;

  if (p == nullptr) {
    return 0;
  }
  if (p) {
    return 0;
  }
  if (!p) {
    return 2;
  }
  if (!!(char *)(void *)p) {
    return 2;
  }
  if (p != (void*)0) {
    return 3;
  }

  bool isNull = p;
  bool notNull = !p;
  bool isNull2 = !!p;
  return 1;
}

int f2(int x) {
  int *nonnull = &x;

  if (!nonnull) { // BAD: `&` can't be null
    return 1;
  }

  if (x) {
    nonnull = nullptr;
  }

  if (!nonnull) { // GOOD
    return 1;
  }
  return 0;
}


extern char *optarg;
int f3(int x) {
  char *dopt;
  dopt = NULL;

  if (x == 1) {
    dopt = optarg;
  }

  if (dopt) { // GOOD
    return 1;
  }
  return 0;
}
