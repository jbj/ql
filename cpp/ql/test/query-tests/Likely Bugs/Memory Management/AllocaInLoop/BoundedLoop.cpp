void *__builtin_alloca(unsigned long sz);
#define alloca __builtin_alloca

void forOnce() {
  for (struct { bool stop; } state = { 0 }; !state.stop; state.stop = 1) {
    alloca(100); // GOOD
  }
}

void forOnce2() {
  bool stop;
  for (stop = 0; !stop; stop = 1) {
    alloca(100); // GOOD
  }
}

void forTwice() {
  for (int i = 0; i < 2; i++) {
    alloca(100); // GOOD
  }
}

void forEver() {
  for (;;) {
    alloca(100); // BAD
  }
}

void doTwice() {
  int i = 0;
  do {
    alloca(100); // GOOD
  } while (++i < 2);
}

void unknownStartingPoint(int i) {
  for (; i < 2; i++) {
    alloca(100); // BAD [NOT DETECTED]
  }
}

int getInt();

void atMostTwice() {
  int i = 0;
  while (!(i >= 2 || getInt())) {
    i++;
    alloca(100); // GOOD
  }
}

void sometimesIncrement() {
  int i = 0;
  while (i < 2) {
    alloca(100); // BAD
    if (getInt()) {
      i++;
    }
  }
}

void upAndDown() {
  for (int i = 0; i < 2; i++) {
    alloca(100); // BAD
    if (getInt()) {
      i--;
    }
  }
}

void largeBound() {
  for (int i = 0; i < 10000; i++) {
    alloca(100); // BAD
  }
}

void nestedAddsUp() {
  for (int i = 0; i < 16; i++) {
    for (int j = 0; j < 16; j++) {
      alloca(100); // BAD [NOT DETECTED]
    }
  }
}

void nestedWithReset() {
  bool stop = 0;

  for (int i = 0; i < 1; i++) {
    stop = 0;
    do {
      stop = 1;
      alloca(100); // GOOD
    } while (!stop);
    stop = 0;
  }
}

void eqFalse() {
  for (int stop = 0; stop == 0; stop = 5) {
    alloca(100); // GOOD
  }
}

void eqFalseFlipped() {
  for (int stop = 0; stop == 0; stop = 0) {
    alloca(100); // BAD
  }
}

void neFalse() {
  for (bool go_on = true; go_on != 0; go_on = false) {
    alloca(100); // GOOD
  }
}

void eqTrue() {
  for (bool go_on = false; go_on == true; go_on = false) {
    alloca(100); // GOOD
  }
}
