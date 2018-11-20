// semmle-extractor-options: -std=c++17

namespace std { typedef unsigned long size_t; }

void* operator new  ( std::size_t count, void* ptr );

namespace placement_new {
  struct HasTwoArgCtor {
    int x;
    HasTwoArgCtor(int a, int b);
  };

  template<typename T, typename... Args>
  void make(T *ptr, Args&&... args) {
    ::new((void *)ptr) HasTwoArgCtor(args...);
  }

  void make_HasTwoArgCtor(HasTwoArgCtor *p) {
    make(p, 1, 2);
  }
}

namespace range_based_for_17 {
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
