#define NULL ((void*)0)
void free(void *pointer);

void null_test_forms(int *ip, long *lp, short *sp, char *cp) {
  if (ip) {
    free(ip);
  }
  if (lp != NULL) {
    delete lp;
  }
  if (sp != 0) {
    delete[] sp;
  }
  if (cp != nullptr) {
    free(cp);
    cp = nullptr;
  }
}

void negatives(int *ip, char *cp, short *sp, long *lp) {
  // Freeing a different pointer than what's checked
  if (ip) {
    free(cp);
  }
  // Inverted check
  if (lp == nullptr) {
    free(lp);
  }
  // This pattern is semantically equivalent to the one we're looking for, but
  // we don't want to give an alert here because the code layout suggests this
  // code might evolve in the future to contain more code after the `free`.
  if (sp == nullptr)
    return;
  free(sp);
}

// TODO: structs
