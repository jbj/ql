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

void static_init() {
  static int x1 = 0;
  ;
  static int x2 = 1;
  ;
  static int x3 = 0 + 0;
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
