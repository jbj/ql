// semmle-extractor-options: -std=c++11

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
