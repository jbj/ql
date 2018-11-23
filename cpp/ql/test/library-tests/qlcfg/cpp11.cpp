// semmle-extractor-options: --c++11

namespace range_based_for_11 {
  void array() {
    int arr[4];
    for (auto &el : arr) {
      el = 0;
    }
  }

  struct Iterator {
    void *pos_data;
    bool operator!=(const Iterator &other);
    Iterator &operator++();
    int &operator*();
  };

  struct Iterable {
    void *container_data;
    Iterator begin();
    Iterator end();
  };

  Iterable getContainer();

  int getFirst() {
    for (auto& el : getContainer()) {
      return el;
    }
    return 0;
  }
}

const int global_const = 5;
int global_int = 5;

void skip_init() {
  static int x1 = 0;
  static int x2 = 1;
  static int x3 = 0 + 0;
  static int *x4 = 0;
  static int *x5 = &x3;
  static int *x6 = (&x3 + 1) - 1;
  static int x7[] = { 0, 1 };
  static int *x8[] = { &x1, &global_int };
  static struct { int x; } x9[] = { { 1 } };

  static const char *s1 = "Hello";
  static char s2[] = "World";
  // TODO: non-POD types that may have constructors and such
}

void run_init() {
  int nonstatic;
  static int x1 = global_int;
  static int *x2 = &nonstatic;
}

namespace lambda {
  void simple(int x) {
    auto closure = [=]() -> int { return x; };
  }

  class Val {
    void *m_data;
  public:
    Val(int);
    Val(const Val &);
  };

  template<typename Fn>
  void apply(Val arg, Fn unaryFunction) {
    unaryFunction(arg);
  }

  template <typename Fn>
  void apply2(Fn binaryFunction, Val arg1, Val arg2) {
    apply(arg2, [=](Val x) { binaryFunction(arg1, x); });
  }

  int doSomething(Val arg1, Val arg2);

  void main() {
    apply2(doSomething, Val(1), Val(2));
  }
}
